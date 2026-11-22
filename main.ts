// Tiny stack VM for make.fun's tiny-stack-vm-01 ISA (see kit ISA.md).
// Runs every /input/<id>/program.bin on its input.bin and writes
// /output/<id>/stdout.bin + /output/<id>/exit.txt. Pure, deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode tables, indexed by opcode byte: immediate length, pops, pushes.
const IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256), KN = new Uint8Array(256);
for (const [o, i, p, u] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3],
  [16, 0, 2, 1], [17, 0, 2, 1], [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1],
  [21, 0, 2, 1], [22, 0, 2, 1], [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1],
  [26, 0, 2, 1], [27, 0, 1, 1], [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1],
  [32, 0, 2, 1], [33, 0, 2, 1], [34, 0, 2, 1],
  [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0], [52, 0, 0, 0],
  [64, 0, 1, 1], [65, 0, 2, 0],
  [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1], [83, 0, 1, 0],
]) { KN[o] = 1; IM[o] = i; PO[o] = p; PU[o] = u; }

function run(P, B) {
  const n = P.length, D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const O = new Uint8Array(65536);
  let sp = 0, cp = 0, ip = 0, pc = 0, st = 0, ol = 0;
  const end = (e) => [e, O.slice(0, ol)];
  for (;;) {
    if (st === 1000000) return end(10);          // step limit
    if (pc < 0 || pc >= n) return end(9);        // pc outside program
    const o = P[pc];
    if (!KN[o]) return end(5);                   // unknown opcode
    const im = IM[o];
    if (pc + im >= n) return end(9);             // immediate cut off
    st++;
    const nx = pc + 1 + im, po = PO[o], pu = PU[o];
    if (sp < po) return end(2);                  // stack underflow
    if (sp - po + pu > 256) return end(3);       // stack overflow
    pc = nx;
    switch (o) {
      case 0: return end(0);                     // HALT
      case 1: D[sp++] = (P[nx - 1] << 24) >> 24; break;              // PUSH8, sign-extended
      case 2: D[sp++] = P[nx - 4] | P[nx - 3] << 8 | P[nx - 2] << 16 | P[nx - 1] << 24; break; // PUSH32 LE
      case 3: sp--; break;                       // POP
      case 4: D[sp] = D[sp - 1]; sp++; break;    // DUP
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break;    // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 23: D[sp - 1] = -D[sp - 1] | 0; break;                   // NEG (wraps)
      case 27: D[sp - 1] = ~D[sp - 1]; break;                       // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (o === 16) r = a + b | 0;                                  // ADD
        else if (o === 17) r = a - b | 0;                             // SUB
        else if (o === 18) r = Math.imul(a, b);                       // MUL, low 32 bits
        else if (o === 19) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : a / b | 0; } // DIV
        else if (o === 20) { if (!b) return end(4); r = b === -1 ? 0 : a % b | 0; }                    // MOD
        else if (o === 21) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }      // DIVU
        else if (o === 22) { if (!b) return end(4); r = (a >>> 0) % (b >>> 0) | 0; }                   // MODU
        else if (o === 24) r = a & b;                                 // AND
        else if (o === 25) r = a | b;                                 // OR
        else if (o === 26) r = a ^ b;                                 // XOR
        else if (o === 28) r = a << (b & 31);                         // SHL
        else if (o === 29) r = a >> (b & 31);                         // SHR, arithmetic
        else if (o === 30) r = a >>> (b & 31) | 0;                    // SHRU, logical
        else if (o === 32) r = a === b ? 1 : 0;                       // EQ
        else if (o === 33) r = a < b ? 1 : 0;                         // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;                       // LTU, unsigned
        sp -= 2; D[sp++] = r; break;
      }
      case 48: case 49: case 50: {                 // JMP / JZ / JNZ
        const rel = ((P[nx - 2] | P[nx - 1] << 8) << 16) >> 16;
        let t = 1;
        if (o !== 48) { const v = D[--sp]; t = o === 49 ? v === 0 : v !== 0; }
        if (t) pc = nx + rel;
        break;
      }
      case 51:                                     // CALL
        if (cp === 64) return end(7);
        C[cp++] = nx; pc = P[nx - 2] | P[nx - 1] << 8; break;
      case 52:                                     // RET
        if (!cp) return end(8);
        pc = C[--cp]; break;
      case 64: {                                   // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a]; break;
      }
      case 65: {                                   // STORE (v addr --)
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2; M[a] = v; break;
      }
      case 80: {                                   // PRINT, decimal, no newline
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) O[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:                                     // PUTC
        if (ol + 1 > 65536) return end(11);
        O[ol++] = D[--sp] & 255; break;
      case 82: D[sp++] = ip < B.length ? B[ip++] : -1; break;        // IN, -1 at EOF
      case 83: return end(D[--sp] & 255);         // EXIT, low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  mkdirSync(join(O, id), { recursive: true });
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  writeFileSync(join(O, id, 'stdout.bin'), r[1]);
  writeFileSync(join(O, id, 'exit.txt'), r[0] + '\n');
}
