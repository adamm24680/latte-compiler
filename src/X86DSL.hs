{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS -Wall #-}
module X86DSL (X86Address(..), X86Label(..), X86Op(..), X86Ins(..), X86Cond(..),
    X86Reg(..), DSLReg(..))
  where

import Text.Printf

data X86Reg = Eax | Ebx | Ecx | Edx | Edi | Esi | Ebp | Esp deriving (Eq, Ord)

instance Show X86Reg where
  show Eax = "eax"
  show Ebx = "ebx"
  show Ecx = "ecx"
  show Edx = "edx"
  show Esi = "esi"
  show Edi = "edi"
  show Ebp = "ebp"
  show Esp = "esp"

data X86Address = AReg X86Reg | AOff X86Reg Int | ALea X86Reg X86Reg Int Int
  deriving (Eq)
instance Show X86Address where
  show (AReg r) = show r
  show (AOff r i) = show r ++ " + " ++ show i
  show (ALea b m mul off) =
    show b ++ " + "++ show mul ++"*"++ show m ++" + "++ show off

newtype X86Label = X86Label String
  deriving (Eq)
instance Show X86Label where
  show (X86Label s) = s

data X86Op = PReg X86Reg | PImm Int | PEAddress X86Address | PLabel X86Label
  deriving (Eq)
instance Show X86Op where
  show (PReg r) = show r
  show (PImm i) = "dword " ++ show i
  show (PEAddress a) = "["++show a++"]"
  show (PLabel l) = show l

data X86Cond = CZ | CNZ | CGE | CLE | CG | CL deriving (Eq)

instance Show X86Cond where
  show CZ = "z"
  show CNZ = "nz"
  show CGE = "ge"
  show CLE = "le"
  show CG = "g"
  show CL = "l"
instance PrintfArg X86Cond where
  formatArg x _ = shows x

data X86Ins =
  Label X86Label |
  Push X86Op |
  Pop X86Op |
  Mov X86Op X86Op |
  Add X86Op X86Op |
  Sub X86Op X86Op |
  Imul X86Op |
  Idiv X86Op |
  Cmp X86Op X86Op |
  Jmp X86Op |
  Jz X86Op |
  Jnz X86Op |
  Call X86Op |
  Ret |
  Setcc X86Cond |
  And X86Reg X86Op |
  Or X86Reg X86Op |
  Neg X86Op |
  Not X86Op

instance PrintfArg X86Op where
  formatArg x _ = shows x

instance Show X86Ins where
  show x = case x of
    Label l -> printf "%s:" $ show l
    Push op -> printf "    push %s" op
    Pop op -> printf "    pop %s" op
    Mov op1 op2 -> printf "    mov %s, %s" op1 op2
    Add op1 op2 -> printf "    add %s, %s" op1 op2
    Sub op1 op2 -> printf "    sub %s, %s" op1 op2
    Cmp op1 op2 -> printf "    cmp %s, %s" op1 op2
    Imul op -> printf "    imul %s" op
    Idiv op -> printf "    idiv %s" op
    Jmp op -> printf "    jmp %s" op
    Jz op -> printf "    jz %s" op
    Jnz op -> printf "    jnz %s" op
    Call op -> printf "    call %s" op
    Ret -> printf "    ret"
    Setcc cond -> printf "    set%s al" cond
    And reg op -> printf "    and %s, %s" (show reg) op
    Or reg op -> printf "    or %s, %s" (show reg) op
    Neg op -> printf "    neg %s" op
    Not op -> printf "    not %s" op



class DSLReg t where
  eax :: t
  ebx :: t
  ecx :: t
  edx :: t
  esi :: t
  edi :: t
  ebp :: t
  esp :: t

instance DSLReg X86Reg where
  eax = Eax
  ebx = Ebx
  ecx = Ecx
  edx = Edx
  esi = Esi
  edi = Edi
  ebp = Ebp
  esp = Esp

instance DSLReg X86Op where
  eax = PReg eax
  ebx = PReg ebx
  ecx = PReg ecx
  edx = PReg edx
  esi = PReg esi
  edi = PReg edi
  ebp = PReg ebp
  esp = PReg esp
