class MathUtil {
  static readonly PI: number = 3;
  static square(x: number): number { return x * x; }
  static sumAll(...xs: number[]): number {
    return xs.reduce((a: number, b: number): number => a + b, 0);
  }
}
console.log(MathUtil.PI, MathUtil.square(6), MathUtil.sumAll(1, 2, 3, 4));
