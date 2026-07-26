const m = new Map<string, number>();
m.set("a", 1);
const v = m.get("a")!;
const obj: { inner?: { z: number } } = { inner: { z: 5 } };
const z = obj.inner!.z;
console.log(v + z);
