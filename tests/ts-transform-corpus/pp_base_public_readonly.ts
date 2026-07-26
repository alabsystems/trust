class User { constructor(public readonly id: number, public name: string) {} }
const u = new User(7, "ada");
console.log(u.id, u.name, JSON.stringify(u));
