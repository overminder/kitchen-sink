/// <reference path="typings/main.d.ts" />
import { greeter, shout, Cat, Dog, } from "./lib";
import sourceMapSupport = require("source-map-support");
sourceMapSupport.install();

shout(new Cat);
shout(new Dog);
shout(null);

greeter("HAI");
greeter(1);
