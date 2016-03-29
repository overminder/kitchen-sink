export const foo = 5;

export default async function bar(x: Promise<void>): Promise<void> {
  await x;
  return;
}

