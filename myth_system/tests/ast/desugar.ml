type nat =
  | O
  | S of nat

type bool =
  | True
  | False

type src =
  | NumS of nat
  | PlusS of src * src
  | MinusS of src * src
  | TrueS
  | FalseS

type opcode =
  | PlusOp
  | MinusOp

type dst =
  | NumD of nat
  | BinopD of opcode * dst * dst
  | BoolD of bool


let desugar : src -> dst |>
{
  NumS(0) => NumD(0)
| NumS(1) => NumD(1)
| PlusS(NumS(0), NumS(1)) => BinopD(PlusOp, NumD(0), NumD(1))
| PlusS(NumS(1), NumS(0)) => BinopD(PlusOp, NumD(1), NumD(0))    
| MinusS(NumS(0), NumS(1)) => BinopD(MinusOp, NumD(0), NumD(1))
| MinusS(NumS(1), NumS(0)) => BinopD(MinusOp, NumD(1), NumD(0))
| TrueS => BoolD(True)
| FalseS => BoolD(False)
} = ?
                       
