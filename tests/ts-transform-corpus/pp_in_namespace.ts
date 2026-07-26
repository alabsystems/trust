namespace Shapes { export class Circle { constructor(public radius: number, private color: string) {} area(): number { return 3.14 * this.radius * this.radius; } tint(): string { return this.color; } } }
const c = new Shapes.Circle(2, "red");
console.log(c.radius, c.area(), c.tint());
