class Base { constructor(public kind: string) {} }
class Widget extends Base { constructor(public readonly id: number) { super("widget"); } }
const w = new Widget(42);
console.log(w.kind, w.id, JSON.stringify(w));
