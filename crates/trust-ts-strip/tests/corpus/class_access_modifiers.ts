class Account {
  public readonly id: number;
  private balance: number;
  protected label: string;
  static count: number = 0;
  constructor(id: number, balance: number) {
    this.id = id;
    this.balance = balance;
    this.label = "acct";
    Account.count++;
  }
  public deposit(amount: number): number {
    this.balance += amount;
    return this.balance;
  }
  private secret(): string { return this.label; }
  reveal(): string { return this.secret(); }
}
const acc = new Account(1, 100);
console.log(acc.id, acc.deposit(50), acc.reveal(), Account.count);
