def greet (s : String) : String := s ++ "!"
def greetLen (n : UInt64) : Nat := (greet "hello").length
