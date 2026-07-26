enum Mix { A, B = "bee", C = 10, D }
console.log(Mix.A, Mix.B, Mix.C, Mix.D);
console.log(Mix[0], Mix[10], Mix[11], JSON.stringify(Mix));
