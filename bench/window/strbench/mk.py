"""String-literal walk encoding bench: base64 (big-endian, 6 bits/char) of a walk Nat, decoded in the kernel."""
import sys
A = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
def b64(N):
    out = []
    while N: out.append(A[N & 63]); N >>= 6
    return "".join(reversed(out)) or "A"
HDR = """noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000

/-- the 6-bit value of a base64 character (A–Z a–z 0–9 + /) -/
def b64v (c : Char) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 63 62 (Nat.beq c.toNat 43))
        (Nat.add c.toNat 4) (Nat.ble 48 c.toNat))
      (Nat.sub c.toNat 65) (Nat.ble 65 c.toNat))
    (Nat.sub c.toNat 71) (Nat.ble 97 c.toNat)

/-- big-endian base64 → ℕ -/
def dec (s : String) : Nat := s.toList.foldl (fun a c => Nat.add (Nat.mul a 64) (b64v c)) 0
"""
def write(name, hexlit, mode):
    N = int(hexlit, 16)
    if mode == "str":
        body = f'theorem t : dec "{b64(N)}" = {hexlit} := by decide +kernel\n'
    else:
        body = f'theorem t : ({hexlit} : Nat) = {hexlit} := by decide +kernel\n'
    open(name, "w").write(HDR + "\n" + body)
if __name__ == "__main__":
    h = open("chunk.hex").read().strip()
    k = int(sys.argv[1]) if len(sys.argv) > 1 else len(h)
    hk = "0x" + h[2:2 + k]
    write(f"S{k}.lean", hk, "str"); write(f"H{k}.lean", hk, "hex")
    print(len(hk), "hex chars ->", len(b64(int(hk, 16))), "base64 chars")
