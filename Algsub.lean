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
