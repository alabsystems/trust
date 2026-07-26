enum Code { Ok = 200, Created = 201, NotFound = 404, Teapot }
console.log(Code.Ok, Code.Created, Code.NotFound, Code.Teapot);
console.log(Code[200], Code[404], Code[405]);
