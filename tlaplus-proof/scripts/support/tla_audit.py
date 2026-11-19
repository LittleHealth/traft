"""Small lexical audit for proof holes; comments and strings are not code."""
import re


def code_only(source):
    result = []
    i = 0
    depth = 0
    quoted = False
    line_comment = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if line_comment:
            if char == '\n':
                line_comment = False
            result.append('\n' if char == '\n' else ' ')
        elif depth:
            if pair == '(*':
                depth += 1
                result.extend('  ')
                i += 1
            elif pair == '*)':
                depth -= 1
                result.extend('  ')
                i += 1
            else:
                result.append('\n' if char == '\n' else ' ')
        elif quoted:
            if char == '\\':
                result.extend('  ')
                i += 1
            else:
                if char == '"':
                    quoted = False
                result.append('\n' if char == '\n' else ' ')
        elif pair == '\\*':
            line_comment = True
            result.extend('  ')
            i += 1
        elif pair == '(*':
            depth = 1
            result.extend('  ')
            i += 1
        elif char == '"':
            quoted = True
            result.append(' ')
        else:
            result.append(char)
        i += 1
    if depth or quoted:
        raise ValueError('Unterminated TLA+ comment or string')
    return ''.join(result)


def holes(source):
    return re.findall(r'\b(?:OMITTED|ADMITTED)\b', code_only(source))


def union_parentheses_violations(source):
    """Reject bare UNION set operands: SANY and TLAPM 1.5 group these differently."""
    code = code_only(source)
    failures = []
    for match in re.finditer(r'\bUNION\s*\{', code):
        start = code.index('{', match.start())
        depth, end = 1, start + 1
        while depth and end < len(code):
            depth += (code[end] == '{') - (code[end] == '}')
            end += 1
        if depth:
            raise ValueError('Unclosed UNION operand')
        if not (code[:match.start()].rstrip().endswith('(')
                and code[end:].lstrip().startswith(')')):
            failures.append(code.count('\n', 0, match.start()) + 1)
    return failures


def dependencies(source):
    code = code_only(source)
    names = set(re.findall(r'\bINSTANCE\s+(\w+)', code))
    for match in re.finditer(r'(?m)^EXTENDS\s+([\w,\s]+?)(?=\n\s*\n|\n[^\s,])', code):
        names.update(re.findall(r'\w+', match[1]))
    return names


def local_closure(directory, module):
    seen = set()
    pending = [module]
    while pending:
        name = pending.pop()
        path = directory / (name + '.tla')
        if name in seen or not path.exists():
            continue
        seen.add(name)
        pending.extend(dependencies(path.read_text()))
    return sorted(seen)


def proof_dependencies(directory, module):
    """Local theorem-bearing imports require independent successful runs.

    TLAPM may use an imported theorem without checking its proof in the run of
    the importing module. A root-module success therefore does not certify
    this closure. Standard-library trust is documented separately.
    """
    return [name for name in local_closure(directory, module)
            if re.search(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION)\b',
                         code_only((directory / (name + '.tla')).read_text()))]
