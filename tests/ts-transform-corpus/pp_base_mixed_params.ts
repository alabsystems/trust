class Rect { constructor(public w: number, h: number, readonly label: string) {} describe(h: number): string { return this.label + ":" + (this.w * h); } }
const r = new Rect(3, 0, "box");
console.log(r.w, r.label, r.describe(5), JSON.stringify(r));
