namespace Shapes { export const pi = 3.14; export class Circle { r: number; constructor(r: number) { this.r = r; } area(): number { return pi * this.r * this.r; } } }
console.log(Shapes.pi, new Shapes.Circle(2).area());
