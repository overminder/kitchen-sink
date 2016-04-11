#!/usr/bin/env node

var fs = require('fs');
var ts = require('typescript');
var fileName = 'react-native.d.ts';
var assert = require('assert');

var stackLevel = 0;
var output = [];
var onIdentifierStack = [];
var isFirstProperty = true;

function keyForValue(v, dict) {
  for (var k in dict) {
    if (dict[k] === v) {
      return k;
    }
  }
}

function enter() {
  return stackLevel++;
}

function leave() {
  --stackLevel;
}

function writeOutput(line) {
  console.log('output ' + line);
  output.push(line);
}

function writeType(ty) {
  writeOutput(' :: ' + ty);
}

function pushOnIdentifier(f) {
  onIdentifierStack.push(f);
}

function onIdentifier(id) {
  var f = onIdentifierStack.pop();
  f(id);
}

function enterInterface(id, tyArgs) {
  id = id + 'O';
  tyArgs = tyArgs.slice();
  tyArgs.push('sup');
  writeOutput('type ' + id + tyArgs.join(' ') + ' {');
}

function leaveInterface() {
  writeOutput('}');
}

function enterProperty() {
}

function leaveProperty() {
}

function doNothing() { }

function writeTypeNode(node) {
  var kindName = keyForValue(node.kind, ts.SyntaxKind);
  switch (node.kind) {
    case ts.SyntaxKind.BooleanKeyword:
      writeType('Boolean');
      break;
    case ts.SyntaxKind.StringKeyword:
      writeType('String');
      break;
    case ts.SyntaxKind.NumberKeyword:
      writeType('Number');
      break;
    case ts.SyntaxKind.VoidKeyword:
      writeType('Unit');
      break;
    case ts.SyntaxKind.AnyKeyword:
      writeType('any');
      break;
    case ts.SyntaxKind.FunctionType:
    default:
      assert(false, 'unknown node: ' + kindName);
      break;
  }
}

function debugPrintNode(node) {
  var kindName = keyForValue(node.kind, ts.SyntaxKind);
  console.log(' '.repeat(stackLevel * 2) + 'debug(' + kindName + ')');
}

function toPs(node) {
  var go = toPs;
  var myLevel = enter();
  var kindName = keyForValue(node.kind, ts.SyntaxKind);
  console.log(' '.repeat(myLevel * 2) + 'toPs(' + kindName + ')');
  switch (node.kind) {
    case ts.SyntaxKind.SourceFile:
      node.statements.forEach(go);
      break;
    case ts.SyntaxKind.DeclareKeyword:
      pushOnIdentifier(doNothing);
      break;
    case ts.SyntaxKind.ModuleDeclaration:
      go(node.body);
      break;
    case ts.SyntaxKind.ModuleBlock:
      node.statements.forEach(go);
      break;
    case ts.SyntaxKind.InterfaceDeclaration: {
      var isFirstProperty = true;
      var tyArgs = node.typeParameters.map(function(node) {
        debugPrintNode(node);
        return node.text.toLowerCase();
      });
      enterInterface(node.name, tyArgs);
      // node.heritageClauses
      node.members.forEach(function(decl) {
        assert(decl.kind === ts.SyntaxKind.PropertySignature);
        if (isFirstProperty) {
          isFirstProperty = false;
          writeOutput(decl.name);
        } else {
          writeOutput(', ' + decl.name);
        }
      });
      writeTypeNode(decl.type);
      break;
    }
    case ts.SyntaxKind.ImportEqualsDeclaration:
      // Ignore
      break;
    default:
      assert(false, 'unknown node: ' + kindName);
  }
  leave();
}

var srcFile = ts.createSourceFile(
  fileName,
  fs.readFileSync(fileName).toString(),
  ts.ScriptTarget.ES6, /*setParentNodes */ true);

toPs(srcFile);

//console.log(toPs);
