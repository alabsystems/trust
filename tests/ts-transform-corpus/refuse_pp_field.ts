class Rect { area: number; constructor(public w: number, readonly label: string) { this.area = w * 5; } }
const r = new Rect(3, "box");
console.log(r.w, r.label, r.area, JSON.stringify(r));
