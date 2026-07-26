enum Weird { "a-b" = 1, normal = 2, "c d" = 3 }
console.log(Weird["a-b"], Weird.normal, Weird["c d"]);
console.log(Weird[1], Weird[2], Weird[3], JSON.stringify(Weird));
