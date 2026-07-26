class Animal { constructor(public name: string) {} }
class Dog extends Animal { constructor(name: string, public breed: string) { super(name); } describe(): string { return this.name + " is a " + this.breed; } }
const d = new Dog("Rex", "Lab");
console.log(d.name, d.breed, d.describe());
