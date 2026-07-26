namespace Api { export interface User { id: number } export type Id = number; export const version = 2; export function idOf(u: User): Id { return u.id; } }
console.log(Api.version, Api.idOf({ id: 7 }), JSON.stringify(Api));
