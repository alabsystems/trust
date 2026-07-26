interface Shape { area(): number; }
abstract class Base implements Shape {
  abstract area(): number;
  describe(): string { return "area=" + this.area(); }
}
class Square extends Base {
  readonly side: number;
  constructor(side: number) { super(); this.side = side; }
  override area(): number { return this.side * this.side; }
}
const sq: Shape = new Square(4);
console.log(sq.area(), (sq as Base).describe());
