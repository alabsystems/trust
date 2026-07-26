function classify(n: number): string {
  return n < 0 ? "neg" : n === 0 ? "zero" : n < 10 ? "small" : "big";
}
const a: boolean = true;
const b: boolean = false;
console.log(classify(-2), classify(0), classify(5), classify(42), a && b, a || b, !a);
