interface Point { x: number; y: number; }
interface Named extends Point { label: string; }
function dist(p: Point): number { return Math.abs(p.x) + Math.abs(p.y); }
const n: Named = { x: 3, y: 4, label: "p" };
console.log(dist(n), n.label);
