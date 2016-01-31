# Anatomy of an x86\_64 instruction

Mostly copied from [osdev: x86\_64 instruction encoding](http://wiki.osdev.org/X86-64_Instruction_Encoding). I just cut off the information a bit so that we can focus on the core part.

    <x86_64-instr> := <legacy-prefix>? <opcode-with-prefix> <ModRM>?
                      <SIB>? <displacement>? <immediate>?

## Legacy prefixes

  What interest us are the operand-size and address-size override prefixes.
  Operand-size supports `16/32/64` bits override and address-size supports
  `32/64` bits override. Disassembler also use this field to decode the rest.

## Opcode with prefixes

Many kinds of opcodes exist. Here we are only interested in the legacy
opcodes:

### Prefix

`0x66, 0xF2 or 0xF3`, mostly used by the SIMD instructions. Just think of
it as a part of the opcode.

### REX prefix

REX stands for Register EXtension. It's used to add 64-bit and another
8 GPRegs into the instruction set. It's only available in long mode.
The encoding is a byte:

     7      0
    [0100WRXB]

<table>
<tr>
<th> Field </th>
<td> W </td>
<td> R </td>
<td> X </td>
<td> B </td>
</tr>
<tr>
<th> Descr </th>
<td> Set to 1 if override to use wide (64-bit) register. </td>
<td> Extension to ModRM.reg </td>
<td> Extension to SIB.index </td>
<td> Extension to ModRM.rm or SIB.base, since those two are mutually
     exclusive.
</td>
</tr>
</table>

This is used when:

- Using `64-bit` operand and the instruction does not default to 64-bit
  operand size.
- Using **extended** registers (R8 - R15, and etc.)
- Using **uniform byte** registers (SPL, BPL, SIL, DIL)

This is NOT used when:

- Using **high byte** registers (AH, CH, BH, DH)

### Opcode

Possible sequences:

    <op>
    0x0F <op>
    0x0F 0x38 <op>
    0x0F 0x3A <op>

Opcode might also specify `ModRM.reg` to be a particular value.

## ModRM and SIB

Those are used to encode operands (up to 2). One of the operand will be a
direct register operand `%reg` and the other can be either nothing,
a direct register operand, an indirect register operand `disp(%reg)`
or a memory address `disp(%reg, %index, %scale)`.

### ModRM

It encodes a register or an opcode extension, plus a register or a memory
address:

    7 6   5 3   2 0
    mod | reg | r/m

<table>
<tr>
<th> mod </th>
<th> reg </th>
<th> rm </th>
</tr>
<tr>
<td> 0b11 means register-direct addressing mode, otherwise indirect. </td>
<td> Either opcode's extension, or the 3-bit register number,
     using REX.R as the extension.
</td>
<td> Register operand, can have a displacement,
     using REX.B as the extension.
</td>
</tr>
</table>

**mod** = `0b11` means direct-addressing `%reg`.

**mod** = `0b00, 0b01, 0b10` means indirect-addressing `disp(%rm)`
where no-displacement, 8-bit displacement or 32-bit displacement will be used
respectively. `rm = SP, BP, R12 and R13` are treated differently:

- When **mod** = `0b00, 0b01 or 0b10` and `rm = SP` or `R12`, **SIB** is used.
- When **mod** = `0b00`, `rm = BP or R13` means `disp32(%rip)`

### SIB

It stands for Scale Index Base. Some specific combinations of values in
ModRM will cause SIB to be used. The encoding is as follows:

    7   6   5   3   2  0
    scale | index | base

<table>
<tr>
<th> scale </th>
<th> index </th>
<th> base </th>
</tr>
<tr>
<td> 1 &lt;&lt; $scale is the scale factor. </td>
<td> index register used in the indirect address mode,
     using REX.X as the extension.
</td>
<td> base register used in the indirect address mode,
     using REX.B as the extension.
</td>
</tr>
</table>

In most of the cases, the operand that **SIB** forms is
`base + (index * scale) + disp`, where `disp` depends on `ModRM.mod` in
the same way as in ModRM.

Index and base registers also have some kind of interferences on the
resulting operand:

- `SP` as **SIB.index** means **SIB.scale** is not used.

- When **ModRM.mod** = `0b00`, `BP` or `R13` as **SIB.base** means
  **SIB.base** is not used.

## Displacement

1, 2, 4 or 8 bytes. 8-byte displacement means that no immediate can be encoded.

## Immediate

1, 2, 4 or 8 bytes. 8-byte immediate means that no displacement can be encoded.

