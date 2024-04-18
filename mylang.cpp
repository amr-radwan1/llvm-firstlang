#include "../include/KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>
#include <iostream>

using namespace llvm::orc;
using namespace std;
using namespace llvm;

class PrototypeAST;

// for parser and lexer
static std::string IdentifierString;
static double NumVal;
static std::map<char, int> BinopPrecedence;

// for codegen
static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<IRBuilder<>> Builder;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::unique_ptr<FunctionPassManager> TheFPM;
static std::unique_ptr<LoopAnalysisManager> TheLAM;
static std::unique_ptr<FunctionAnalysisManager> TheFAM;
static std::unique_ptr<CGSCCAnalysisManager> TheCGAM;
static std::unique_ptr<ModuleAnalysisManager> TheMAM;
static std::unique_ptr<PassInstrumentationCallbacks> ThePIC;
static std::unique_ptr<StandardInstrumentations> TheSI;
static std::map<std::string, Value *> NamedValues;
static ExitOnError ExitOnErr;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

enum Token {
  tok_eof = -1,

  // commands
  tok_def = -2,
  tok_extern = -3,

  // primary
  tok_identifier = -4,
  tok_number = -5,
  tok_if = -6,
  tok_then = -7,
  tok_else = -8,
  tok_for = -9,
  tok_in = 10,
  tok_binary = -11,
  tok_unary = -12,
};

static void InitializeModuleAndManagers();
Function *getFunction(std::string Name);

void LogError(const char *Str) { fprintf(stderr, "LogError: %s\n", Str); }

static int gettok() {
  static int LastChar = ' ';

  // skip spaces
  while (isspace(LastChar)) {
    // Get single character
    LastChar = getchar();
  }

  // get identifier
  if (isalpha(LastChar)) {
    IdentifierString = LastChar;

    // Get rest of string
    while (isalnum(LastChar = getchar())) {
      IdentifierString += LastChar;
    }

    if (IdentifierString == "def") {
      return tok_def;
    }

    if (IdentifierString == "extern") {
      return tok_extern;
    }

    if (IdentifierString == "if") {
      return tok_if;
    }

    if (IdentifierString == "then") {
      return tok_then;
    }

    if (IdentifierString == "else") {
      return tok_else;
    }

    if (IdentifierString == "for") {
      return tok_for;
    }

    if (IdentifierString == "in") {
      return tok_in;
    }

    if (IdentifierString == "binary") {
      return tok_binary;
    }

    if (IdentifierString == "unary") {
      return tok_unary;
    }

    return tok_identifier;
  }

  if (isdigit(LastChar) || LastChar == '.') {
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = getchar();
    } while (isdigit(LastChar) || LastChar == '.');
    NumVal = strtod(NumStr.c_str(), 0);
    return tok_number;
  }

  if (LastChar == '#') {
    do {
      LastChar = getchar();
    } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

    if (LastChar != EOF) {
      return gettok();
    }
  }

  if (LastChar == EOF) {
    return tok_eof;
  }

  int ThisChar = LastChar;
  LastChar = getchar();
  return ThisChar;
}

// int main(){
//   while(true) {
//     int tok = gettok();
//     cout << "got token: " << tok << endl;
//   }
// }

class ExprAST {
public:
  virtual ~ExprAST() {}
  // reason for = 0: every subclass has to give an implementation for this
  // method
  virtual Value *codegen() = 0;
};

class NumberExprAST : public ExprAST {
  double Val;

public:
  NumberExprAST(double V) : Val(V) {}
  virtual Value *codegen() override;
};

Value *NumberExprAST::codegen() {
  return ConstantFP::get(*TheContext, APFloat(Val));
}

class VariableExprAST : public ExprAST {
  std::string Name;

public:
  VariableExprAST(const std::string &Name) : Name(Name) {}
  virtual Value *codegen();
};

Value *VariableExprAST::codegen() {
  Value *V = NamedValues[Name];
  if (!V) {
    LogError("Unknown variable name");
  }
  return V;
}

class BinaryExprAST : public ExprAST {
  char Op; // + - * / < >
  std::unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
      : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}

  virtual Value *codegen();
};

Value *BinaryExprAST::codegen() {
  Value *L = LHS->codegen();
  Value *R = RHS->codegen();
  if (!L || !R) {
    return nullptr;
  }

  switch (Op) {
  case '+':
    return Builder->CreateFAdd(L, R, "addtmp");
  case '-':
    return Builder->CreateFSub(L, R, "subtmp");
  case '*':
    return Builder->CreateFMul(L, R, "multmp");
  case '<':
    L = Builder->CreateFCmpULT(L, R, "cmptmp");
    return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
  default:
    break;
  }

  // concatenate operator (such as @) to "binary" as func name
  Function *F = getFunction(std::string("binary") + Op);
  assert(F && "binary operator not found");

  Value *Ops[] = {L, R};
  return Builder->CreateCall(F, Ops, "binop");
}

class UnaryExprAST : public ExprAST {
  char Opcode;
  std::unique_ptr<ExprAST> Operand;

public:
  UnaryExprAST(char Opcode, std::unique_ptr<ExprAST> Operand)
      : Opcode(Opcode), Operand(std::move(Operand)) {}

  Value *codegen() override;
};

Value *UnaryExprAST::codegen() {
  Value *OperandV = Operand->codegen();
  if (!OperandV) {
    return nullptr;
  }

  Function *F = getFunction(std::string("unary") + Opcode);
  if (!F) {
    LogError("Unknown unary operator");
    return nullptr;
  }

  return Builder->CreateCall(F, OperandV, "unop");
}

// funcA() { call funcB(a, b, c) }
// funcB(int, int, int)

class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  CallExprAST(const std::string &Callee,
              std::vector<std::unique_ptr<ExprAST>> Args)
      : Callee(Callee), Args(std::move(Args)) {}

  virtual Value *codegen();
};

Value *CallExprAST::codegen() {
  Function *CalleeF = getFunction(Callee);

  if (!CalleeF) {
    LogError("Unknown function referenced");
    return nullptr;
  }

  if (CalleeF->arg_size() != Args.size()) {
    LogError("Incorrect # arguments passed");
    return nullptr;
  }

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; i++) {
    ArgsV.push_back(Args[i]->codegen());
    if (!ArgsV.back()) {
      return nullptr;
    }
  }

  return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
}

// function signature eg. getSum(x y)
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;
  bool IsOperator;
  unsigned Precedence;

public:
  PrototypeAST(
      const std::string &Name,
      std::vector<std::string> Args,
      bool IsOperator = false,
      unsigned Prec = 0)
      : Name(Name),
      Args(std::move(Args)),
      IsOperator(IsOperator),
      Precedence(Prec) {}

  Function *codegen();
  const std::string &getName() const { return Name; }

  bool isUnaryOp() const { return IsOperator && Args.size() == 1; }
  bool isBinaryOp() const { return IsOperator && Args.size() == 2; }

  char getOperatorName() const {
    assert(isUnaryOp() || isBinaryOp());
    return Name[Name.size() - 1];
  }

  unsigned getBinaryPrecedence() const { return Precedence; }
};

Function *PrototypeAST::codegen() {
  std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));

  FunctionType *FT =
      FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);
  Function *F =
      Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

  unsigned Idx = 0;
  for (auto &Arg : F->args()) {
    Arg.setName(Args[Idx++]);
  }

  return F;
}

/// FunctionAST - This class represents a function definition itself.
class FunctionAST {
  std::unique_ptr<PrototypeAST> Proto;
  std::unique_ptr<ExprAST> Body;

public:
  FunctionAST(std::unique_ptr<PrototypeAST> Proto,
              std::unique_ptr<ExprAST> Body)
      : Proto(std::move(Proto)), Body(std::move(Body)) {}

  virtual Function *codegen();
};

Function *FunctionAST::codegen() {
  auto &P = *Proto;
  FunctionProtos[Proto->getName()] = std::move(Proto);
  Function *TheFunction = getFunction(P.getName());

  if (!TheFunction) {
    return nullptr;
  }

  if (P.isBinaryOp()) {
    BinopPrecedence[P.getOperatorName()] = P.getBinaryPrecedence();
  }

  BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
  Builder->SetInsertPoint(BB);

  NamedValues.clear();
  for (auto &Arg : TheFunction->args()) {
    NamedValues[std::string(Arg.getName())] = &Arg;
  }

  Value *RetVal = Body->codegen();
  if (RetVal) {
    Builder->CreateRet(RetVal);

    verifyFunction(*TheFunction);

    // run optimizer on the function
    TheFPM->run(*TheFunction, *TheFAM);

    return TheFunction;
  }

  // if we didnt get a body then clean up what we did as error handling
  TheFunction->eraseFromParent();

  if (P.isBinaryOp()) {
    BinopPrecedence.erase(P.getOperatorName());
  }
    
  return nullptr;
}

class IfExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, Then, Else;

public:
  IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then,
            std::unique_ptr<ExprAST> Else)
      : Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}

  Value *codegen() override;
};

Value *IfExprAST::codegen() {
  Value *CondV = Cond->codegen();
  if (!CondV) {
    return nullptr;
  }

  // Builder - builds llvm IR
  // FCmp - floating point compare
  // Compares condition with 0 because 0 is falsey
  CondV = Builder->CreateFCmpONE(
      CondV, ConstantFP::get(*TheContext, APFloat(0.0)), "ifcond");

  Function *TheFunction = Builder->GetInsertBlock()->getParent();
  BasicBlock *ThenBB = BasicBlock::Create(*TheContext, "then", TheFunction);
  BasicBlock *ElseBB = BasicBlock::Create(*TheContext, "else");
  BasicBlock *MergeBB = BasicBlock::Create(*TheContext, "ifcont");

  // Conditional branching
  Builder->CreateCondBr(CondV, ThenBB, ElseBB);

  Builder->SetInsertPoint(ThenBB);
  Value *ThenV = Then->codegen();
  if (!ThenV) {
    return nullptr;
  }

  Builder->CreateBr(MergeBB);
  ThenBB = Builder->GetInsertBlock();

  TheFunction->insert(TheFunction->end(), ElseBB);
  Builder->SetInsertPoint(ElseBB);
  Value *ElseV = Else->codegen();
  if (!ElseV) {
    return nullptr;
  }

  Builder->CreateBr(MergeBB);

  ElseBB = Builder->GetInsertBlock();

  TheFunction->insert(TheFunction->end(), MergeBB);
  Builder->SetInsertPoint(MergeBB);

  PHINode *PN = Builder->CreatePHI(Type::getDoubleTy(*TheContext), 2, "iftmp");
  // if its coming from Then branch, use value from then and vice versa
  PN->addIncoming(ThenV, ThenBB);
  PN->addIncoming(ElseV, ElseBB);
  return PN;
}

// for i = 0, i < 10, 1.0 in
//   putchard(i)
class ForExprAST : public ExprAST {
  std::string VarName;
  std::unique_ptr<ExprAST> Start, End, Step, Body;

public:
  ForExprAST(const std::string &VarName, std::unique_ptr<ExprAST> Start,
             std::unique_ptr<ExprAST> End, std::unique_ptr<ExprAST> Step,
             std::unique_ptr<ExprAST> Body)
      : VarName(VarName), Start(std::move(Start)), End(std::move(End)),
        Step(std::move(Step)), Body(std::move(Body)) {}

  Value *codegen() override;
};

static int CurTok;
static int getNextToken() { return CurTok = gettok(); }

static std::unique_ptr<ExprAST> ParseNumberExpr() {
  auto Result = std::make_unique<NumberExprAST>(NumVal);
  getNextToken();
  return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseExpression();

static std::unique_ptr<ExprAST> ParseParenExpr() {
  getNextToken(); // eat '('
  auto V = ParseExpression();
  if (!V) {
    return nullptr;
  }

  if (CurTok == ')') {
    getNextToken(); // eat )
  } else {
    LogError("expected ')'");
    return nullptr;
  }

  return V;
}

static std::unique_ptr<ExprAST> ParseIdentifierOrCallExpr() {
  std::string IdName = IdentifierString;

  getNextToken(); // eat identifier
  // num1 + num2
  if (CurTok == '(') {
    getNextToken();

    std::vector<std::unique_ptr<ExprAST>> Args;
    while (true) {
      auto Arg = ParseExpression();
      if (Arg) {
        Args.push_back(std::move(Arg));
      } else {
        return nullptr;
      }

      if (CurTok == ')') {
        getNextToken(); // eat ')'
        break;
      } else if (CurTok == ',') {
        getNextToken(); // eat ','
        continue;
      } else {
        LogError("Expected ')' or ',' in argument list");
        return nullptr;
      }
    }

    return std::make_unique<CallExprAST>(IdName, std::move(Args));
  }
  return std::make_unique<VariableExprAST>(IdName);
}

static std::unique_ptr<ExprAST> ParseIfExpr() {
  getNextToken(); // eat the if

  auto Cond = ParseExpression();
  if (!Cond) {
    return nullptr;
  }

  if (CurTok != tok_then) {
    LogError("expected then");
    return nullptr;
  }

  getNextToken(); // eat the then

  auto Then = ParseExpression();
  if (!Then) {
    return nullptr;
  }

  if (CurTok != tok_else) {
    LogError("expected else");
    return nullptr;
  }

  getNextToken(); // eat the else

  auto Else = ParseExpression();
  if (!Else) {
    return nullptr;
  }

  return std::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
                                     std::move(Else));
}

static std::unique_ptr<ExprAST> ParseForExpr() {
  getNextToken(); // eat for

  if (CurTok != tok_identifier) {
    LogError("expected identifier after for");
    return nullptr;
  }

  std::string IdName = IdentifierString;
  getNextToken(); // eat identifier (such as i)

  if (CurTok != '=') {
    LogError("expected '=' after for");
    return nullptr;
  }
  getNextToken(); // eat equals

  auto Start = ParseExpression();
  if (!Start) {
    return nullptr;
  }

  if (CurTok != ',') {
    LogError("expected ',' after for start value");
    return nullptr;
  }
  getNextToken();

  auto End = ParseExpression();
  if (!End) {
    return nullptr;
  }

  // step is optional but if comma is there and no step mentioned then error
  std::unique_ptr<ExprAST> Step;
  if (CurTok == ',') {
    getNextToken();
    Step = ParseExpression();
    if (!Step) {
      return nullptr;
    }
  }
  if (CurTok != tok_in) {
    LogError("expected 'in' after for");
    return nullptr;
  }
  getNextToken();

  auto Body = ParseExpression();
  if (!Body) {
    return nullptr;
  }

  return std::make_unique<ForExprAST>(IdName, std::move(Start), std::move(End),
                                      std::move(Step), std::move(Body));
}

Value *ForExprAST::codegen() {
  Value *StartVal = Start->codegen();
  if (!StartVal) {
    return nullptr;
  }

  Function *TheFunction = Builder->GetInsertBlock()->getParent();
  BasicBlock *EntryBB = Builder->GetInsertBlock();
  BasicBlock *LoopBB = BasicBlock::Create(*TheContext, "loop", TheFunction);

  Builder->CreateBr(LoopBB);

  Builder->SetInsertPoint(LoopBB);

  PHINode *Variable =
      Builder->CreatePHI(Type::getDoubleTy(*TheContext), 2, VarName.c_str());
  Variable->addIncoming(StartVal, EntryBB);

  Value *OldVal = NamedValues[VarName];
  NamedValues[VarName] = Variable;

  if (!Body->codegen()) {
    return nullptr;
  }

  Value *StepVal = nullptr;
  if (Step) {
    StepVal = Step->codegen();
    if (!StepVal) {
      return nullptr;
    }
  } else {
    // if no step then default step is 1
    StepVal = ConstantFP::get(*TheContext, APFloat(1.0));
  }

  Value *NextVar = Builder->CreateFAdd(Variable, StepVal, "nextvar");

  Value *EndCond = End->codegen();
  if (!EndCond) {
    return nullptr;
  }

  EndCond = Builder->CreateFCmpONE(
      EndCond, ConstantFP::get(*TheContext, APFloat(0.0)), "loopcond");

  BasicBlock *LoopEndBB = Builder->GetInsertBlock();
  BasicBlock *AfterBB =
      BasicBlock::Create(*TheContext, "afterloop", TheFunction);

  Builder->CreateCondBr(EndCond, LoopBB, AfterBB);
  Builder->SetInsertPoint(AfterBB);

  Variable->addIncoming(NextVar, LoopEndBB);

  if (OldVal) {
    NamedValues[VarName] = OldVal;
  } else {
    NamedValues.erase(VarName);
  }

  return Constant::getNullValue(Type::getDoubleTy(*TheContext));
}

// Primary is number or identifer or something like (2+3). (unary expression)
static std::unique_ptr<ExprAST> ParsePrimary() {
  switch (CurTok) {
  case tok_for:
    return ParseForExpr();
  case tok_if:
    return ParseIfExpr();
  case tok_identifier:
    return ParseIdentifierOrCallExpr();
  case tok_number:
    return ParseNumberExpr();
  case '(':
    return ParseParenExpr();
  default:
    LogError("unknown token when expecting an expression");
    return nullptr;
  }
}

static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0)
    return -1;
  return TokPrec;
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS);

static std::unique_ptr<ExprAST> ParseUnary() {
  if (!isascii(CurTok) || CurTok == '(' || CurTok == ',') {
    return ParsePrimary();
  }

  int Opc = CurTok;
  getNextToken();
  // recursion in case there's more than one unary operator
  if (auto Operand = ParseUnary()) {
    return std::make_unique<UnaryExprAST>(Opc, std::move(Operand));
  }
  return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression() {
  auto LHS = ParseUnary();
  if (LHS) {
    return ParseBinOpRHS(0, std::move(LHS));
  }

  return nullptr;
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS) {
  while (true) {
    int TokPrec = GetTokPrecedence();

    if (TokPrec < ExprPrec) {
      return LHS;
    } else {
      int BinOp = CurTok;
      getNextToken();
      auto RHS = ParseUnary();
      if (RHS) {
        int NextPrec = GetTokPrecedence();
        if (TokPrec < NextPrec) {
          RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
          if (!RHS) {
            return nullptr;
          }
        }
        LHS = std::make_unique<BinaryExprAST>(BinOp, std::move(LHS),
                                              std::move(RHS));
      } else {
        return nullptr;
      }
    }
  }
}

// parse function signature
// func (x y)
// binary@ 5 (x y)
// unary# (x)
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  std::string FnName = IdentifierString;

  unsigned Kind = 0; // 0 = identifier, 1 = unary, 2 = binary.
  unsigned BinaryPrecedence = 30;

  switch (CurTok) {
  case tok_identifier:
    FnName = IdentifierString;
    Kind = 0;
    getNextToken();
    break;
  case tok_unary:
    getNextToken();
    if (!isascii(CurTok)) {
      LogError("Expected unary operator");
      return nullptr;
    }
    FnName = "unary";
    FnName += (char)CurTok;
    Kind = 1;
    getNextToken();
    break;
  case tok_binary:
    getNextToken();
    if (!isascii(CurTok)) {
      LogError("Expected binary operator");
      return nullptr;
    }
    FnName = "binary";
    FnName += (char)CurTok;
    Kind = 2;
    getNextToken();

    if (CurTok == tok_number) {
      if (NumVal < 1 || NumVal > 100) {
        LogError("Invalid precedence: must be 1..100");
        return nullptr;
      }
      BinaryPrecedence = (unsigned)NumVal;
      getNextToken();
    }
    break;
  default:
    LogError("Expected function name in prototype");
    return nullptr;
  }

  if (CurTok != '(') {
    LogError("Expected '(' in protoype");
    return nullptr;
  }

  std::vector<std::string> ArgNames;
  while (getNextToken() == tok_identifier) {
    ArgNames.push_back(IdentifierString);
  }

  if (CurTok != ')') {
    LogError("Expected ')' in prototype");
    return nullptr;
  }

  getNextToken();

  if (Kind != 0 && ArgNames.size() != Kind) {
    LogError("Invalid number of operands for operator");
    return nullptr;
  }

  return std::make_unique<PrototypeAST>(FnName, ArgNames, Kind != 0,
                                        BinaryPrecedence);
}

// parse function definition/body
static std::unique_ptr<FunctionAST> ParseDefinition() {
  getNextToken();
  auto Proto = ParsePrototype();
  if (!Proto) {
    return nullptr;
  }

  auto E = ParseExpression();
  if (E) {
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }

  return nullptr;
}

// parse extern function
static std::unique_ptr<PrototypeAST> ParseExtern() {
  getNextToken();
  return ParsePrototype();
}

//
static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
  auto E = ParseExpression();
  if (E) {
    auto Proto = std::make_unique<PrototypeAST>("__anon_expr",
                                                std::vector<std::string>());
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }
  return nullptr;
}

static void HandleDefinition() {
  if (auto FnAST = ParseDefinition()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read function definition:\n");
      FnIR->print(errs());
      fprintf(stderr, "\n");
      ExitOnErr(TheJIT->addModule(
          ThreadSafeModule(std::move(TheModule), std::move(TheContext))));
      InitializeModuleAndManagers();
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleExtern() {
  if (auto ProtoAST = ParseExtern()) {
    if (auto *FnIR = ProtoAST->codegen()) {
      fprintf(stderr, "Read extern: \n");
      FnIR->print(errs());
      fprintf(stderr, "\n");
      FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (auto FnAST = ParseTopLevelExpr()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read top level expression\n");
      FnIR->print(errs());
      fprintf(stderr, "\n");

      // Create a ResourceTracker to track JIT'd memory allocated to our
      // anonymous expression -- that way we can free it after executing.
      auto RT = TheJIT->getMainJITDylib().createResourceTracker();

      auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
      ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
      InitializeModuleAndManagers();

      // Search the JIT for the __anon_expr symbol.
      auto ExprSymbol = ExitOnErr(TheJIT->lookup("__anon_expr"));

      // Get the symbol's address and cast it to the right type (takes no
      // arguments, returns a double) so we can call it as a native function.
      double (*FP)() = ExprSymbol.getAddress().toPtr<double (*)()>();
      fprintf(stderr, "\nEvaluated to %f\n", FP());

      // Delete the anonymous expression module from the JIT.
      ExitOnErr(RT->remove());
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
  while (true) {
    fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:
      return;
    case ';': // ignore top-level semicolons.
      getNextToken();
      break;
    case tok_def:
      HandleDefinition();
      break;
    case tok_extern:
      HandleExtern();
      break;
    default:
      HandleTopLevelExpression();
      break;
    }
    fprintf(stderr, "\n");
  }
}

static void InitializeModuleAndManagers() {
  // Open a new context and module.
  TheContext = std::make_unique<LLVMContext>();
  TheModule = std::make_unique<Module>("my cool JIT", *TheContext);
  TheModule->setDataLayout(TheJIT->getDataLayout());

  // Create a new builder for the module.
  Builder = std::make_unique<IRBuilder<>>(*TheContext);

  // Create new pass and analysis managers.
  TheFPM = std::make_unique<FunctionPassManager>();
  TheLAM = std::make_unique<LoopAnalysisManager>();
  TheFAM = std::make_unique<FunctionAnalysisManager>();
  TheCGAM = std::make_unique<CGSCCAnalysisManager>();
  TheMAM = std::make_unique<ModuleAnalysisManager>();
  ThePIC = std::make_unique<PassInstrumentationCallbacks>();
  TheSI = std::make_unique<StandardInstrumentations>(*TheContext,
                                                     /*DebugLogging*/ true);
  TheSI->registerCallbacks(*ThePIC, TheMAM.get());

  // Add transform passes.
  // Do simple "peephole" optimizations and bit-twiddling optzns.
  TheFPM->addPass(InstCombinePass());
  // Reassociate expressions.
  TheFPM->addPass(ReassociatePass());
  // Eliminate Common SubExpressions.
  TheFPM->addPass(GVNPass());
  // Simplify the control flow graph (deleting unreachable blocks, etc).
  TheFPM->addPass(SimplifyCFGPass());

  // Register analysis passes used in these transform passes.
  PassBuilder PB;
  PB.registerModuleAnalyses(*TheMAM);
  PB.registerFunctionAnalyses(*TheFAM);
  PB.crossRegisterProxies(*TheLAM, *TheFAM, *TheCGAM, *TheMAM);
}

Function *getFunction(std::string Name) {
  // First, see if the function has already been added to the current module.
  if (auto *F = TheModule->getFunction(Name)){
    return F;
  }

  // If not, check whether we can codegen the declaration from some existing
  // prototype.
  auto FI = FunctionProtos.find(Name);
  if (FI != FunctionProtos.end()){
    return FI->second->codegen();
  }
    

  // If no existing prototype exists, return null.
  return nullptr;
}

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

/// putchard - putchar that takes a double and returns 0.
extern "C" DLLEXPORT double putchard(double X) {
  fputc((char)X, stderr);
  return 0;
}

int main() {
  InitializeNativeTarget();
  InitializeNativeTargetAsmPrinter();
  InitializeNativeTargetAsmParser();

  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40; // highest.

  // Prime the first token.
  fprintf(stderr, "ready> ");
  getNextToken();

  TheJIT = ExitOnErr(KaleidoscopeJIT::Create());

  InitializeModuleAndManagers();

  // Run the main "interpreter loop" now.
  MainLoop();
  TheModule->print(errs(), nullptr);

  return 0;
}

// SSA - Static Single Assignment form
// Requires that every variable can only be assigned once
// Reason why LLVM chose it is because if code is written in SSA it allows
// for code optimizations. check wikipedia
