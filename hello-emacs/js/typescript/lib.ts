export function greeter(person: string | number) {
  return "Hello, " + person;
}

let user = "Jane";

export function test() {
  console.log(greeter(user));
}

interface Animal {
  shout();
}

export class Dog implements Animal {
  shout() {
    console.log("Woof");
  }
}

export class Cat implements Animal {
  shout() {
    console.log("Meow");
  }
}

export function shout(a: Animal) {
  a.shout();
}
