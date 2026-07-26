interface Dict { [key: string]: number; }
class Registry {
  [slot: string]: number;
  size: number = 0;
}
const d: Dict = { a: 1, b: 2 };
const r = new Registry();
r.x = 5;
console.log(d.a + d.b, r.x);
