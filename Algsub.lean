<<<<<<< HEAD
import Algsub.Basic
=======
import Algsub.Parser
open Lean Elab Term

partial def main : IO Unit := do{
  IO.print "> ";
  let stdin ← IO.getStdin;
  let line ← stdin.getLine;
  let trimmed := line.dropEndWhile Char.isWhitespace;
  if trimmed.beq ":q"
    then pure ()
    else
    main;
}
>>>>>>> 2a25d7c (- Add scratch of automata encoding of types)
