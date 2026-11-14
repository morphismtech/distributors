/// <reference lib="es2020" />
/** A declaration file, of every kind of declaration & type. */
import "polyfill";
import type { A, B as C, type D } from "./types";
import Default, * as Everything from "everything";
import Fs = require("fs");
import Inner = Outer.Inner;
export type Alias<T extends string = "a", in out U = T,> =
  | T
  | readonly U[]
  | keyof T
  | unique symbol;
export type Conditional<T> = T extends (infer U extends string)[] ? U : never;
export type Mapped<T> = { -readonly [K in keyof T as `get${string & K}`]+?: T[K] };
export type Templated = `prefix-${number}-middle-${string}-suffix`;
export type Functions = {
  (x: number, ...rest: string[]): void
  new (x?: number): Functions,
  method?<T>(this: Window, { a, b: c }: T, [d, ...e]: T[]): asserts this is T;
  readonly [key: string]: unknown;
  get value(): number;
  set value(v: number);
  "quoted name": 1;
  0: -1.5;
  [Symbol.iterator](): Iterator<bigint>;
  big: 10n;
};
export type Tuple = [name: string, age?: number, ...rest: boolean[]];
export type Queried = typeof globalThis.console & typeof import("module").Thing<string>;
export type Ctor = abstract new () => object;
export type Guard = (value: unknown) => value is string;
export type Intrinsic = intrinsic;
// Interfaces & classes.
export interface Shape<T> extends Base, Other<T> {
  readonly kind: "shape";
  area(): number;
  [index: number]: T
}
export declare abstract class Circle extends Shape<number> implements Round {
  #private;
  private static readonly instances: number;
  protected radius: number;
  constructor(radius: number);
  abstract area(): number;
  get diameter(): number;
}
export declare function overloaded(x: string): string;
export declare function overloaded(x: number): number;
declare const answer = 42, question: string;
declare let mutable: boolean;
export declare const enum Direction {
  Up = 1,
  Down = -1,
  Unknown,
}
declare namespace Outer.Middle {
  namespace Inner {
    type Deep = "deep";
  }
}
declare module "ambient" {
  export = Ambient;
}
declare module "shorthand";
declare global {
  interface Window {
    extra: string;
  }
}
export default Circle;
export as namespace Library;
export { A as Renamed, type B } from "./types";
export * as Namespace from "./namespace";
export type { Shape as Shaped };
