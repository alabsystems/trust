namespace Geo { export class Point { x: number; y: number; constructor(x: number, y: number) { this.x = x; this.y = y; } dist(): number { return Math.sqrt(this.x * this.x + this.y * this.y); } } }
const p = new Geo.Point(3, 4);
console.log(p.dist(), p.x, p.y);
