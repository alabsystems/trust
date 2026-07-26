class Point { constructor(private x: number, private y: number) {} sum(): number { return this.x + this.y; } }
const p = new Point(3, 4);
console.log(p.sum());
