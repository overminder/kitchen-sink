import * as S from '../shared';

export function foo(): string {
  return 'bar';
}

export function bar(): S.Foo {
  return { value: foo() };
}

