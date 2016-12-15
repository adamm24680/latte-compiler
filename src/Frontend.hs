module Frontend
    (getRepr)
    where

import ErrM
import ParLatte
import PrintLatte
import AbsLatte



parse :: String -> Err Program
parse = pProgram . myLexer

getRepr:: Show a => String -> Err a
getRepr = undefined
