class Box<T> {
  value: T;
  constructor(v: T) { this.value = v; }
  get(): T { return this.value; }
}
const bn = new Box<number>(42);
const bs = new Box<string>("hi");
console.log(bn.get(), bs.get());
