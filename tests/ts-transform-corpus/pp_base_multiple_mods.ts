class Config { constructor(protected readonly host: string, public port: number, private secret: string) {} url(): string { return this.host + ":" + this.port; } reveal(): string { return this.secret; } }
const c = new Config("localhost", 8080, "s3cr3t");
console.log(c.url(), c.reveal(), c.port);
