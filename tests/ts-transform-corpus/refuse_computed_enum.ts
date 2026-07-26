function seed(): number { return 5; }
enum E { A = seed(), B = A + 1 }
console.log(E.A, E.B);
