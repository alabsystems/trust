enum Flags { Read = 0x1, Write = 0x2, Exec = 0x4, Neg = -8, After }
console.log(Flags.Read, Flags.Write, Flags.Exec, Flags.Neg, Flags.After);
console.log(Flags[1], Flags[-8], Flags[-7]);
