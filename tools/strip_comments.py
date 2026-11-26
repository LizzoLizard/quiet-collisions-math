"""Print a Lean 4 file with all comments blanked out (nested /- -/ and --).
Used by verify.sh so that words like `sorry` inside comments are not flagged."""
import sys

def code_only(src):
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth = 0
            while i < n:
                if src.startswith('/-', i): depth += 1; i += 2
                elif src.startswith('-/', i):
                    depth -= 1; i += 2
                    if depth == 0: break
                else:
                    out.append('\n' if src[i] == '\n' else ' '); i += 1
        elif src.startswith('--', i):
            while i < n and src[i] != '\n': i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1]); i = j + 1
        else:
            out.append(src[i]); i += 1
    return ''.join(out)

if __name__ == '__main__':
    sys.stdout.write(code_only(open(sys.argv[1], encoding='utf-8').read()))
