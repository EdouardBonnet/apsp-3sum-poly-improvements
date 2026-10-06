#!/usr/bin/env python3
"""Reproduce the Lax packaging from the unchanged, pinned upstream sources.

Copyright 2026 Édouard Bonnet. SPDX-License-Identifier: Apache-2.0
This script copies Apache-2.0 sources and records the changes in every copy.
"""
from pathlib import Path
import re
import argparse
from functools import lru_cache

ROOT = Path(__file__).resolve().parent
UP = ROOT.parent
C = 'Lax350013'
P = C + 'Proofs'
PIN = 'e1a4e6508154ea59f030480661590a9fe3018011'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='verify reproducibility without writing')
CHECK = parser.parse_args().check
END = (UP / 'EndStatement.lean').read_text()
PAPER = (UP / 'PaperStatements.lean').read_text()
HEADER = END[:END.index('-/') + 2]
MATH = '\n'.join(line.replace('public import', 'import') for line in PAPER.splitlines()
                 if line.startswith('public import Mathlib.'))


@lru_cache(maxsize=16)
def mask_comments(text):
    chars = list(text)
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            chars[i:i+2] = '  '
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            chars[i:i+2] = '  '
            i += 2
        elif depth:
            if text[i] != '\n':
                chars[i] = ' '
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            if j < 0:
                j = len(text)
            chars[i:j] = ' ' * (j - i)
            i = j
        else:
            i += 1
    return ''.join(chars)


def decl_span(text, name):
    masked = mask_comments(text)
    pat = r'(?m)^(?:(?:noncomputable|private|protected) )*(?:def|abbrev|structure|inductive|theorem|lemma) ' + re.escape(name) + r'(?=[\s:{(])'
    m = re.search(pat, masked)
    if not m:
        raise ValueError(f'missing declaration: {name}')
    following = re.search(r'(?m)^(?:@\[|(?:noncomputable|private|protected) |def |abbrev |structure |inductive |theorem |lemma |instance |namespace |end\b|section |open |attribute |set_option )', masked[m.end():])
    end = m.end() + following.start() if following else len(text)
    # Remove the docstrings and section comments introducing the next command.
    tail = text[m.start():end].rstrip()
    while tail.endswith('-/'):
        comment_start = max(tail.rfind('\n/--'), tail.rfind('\n/-!'), tail.rfind('\n/-\n'))
        if comment_start < 0:
            break
        tail = tail[:comment_start].rstrip()
    return m.start(), m.start() + len(tail)


def decl(text, name):
    a, b = decl_span(text, name)
    before = text[:a].rstrip()
    doc = ''
    if before.endswith('-/'):
        d = before.rfind('/--')
        if d >= 0 and before[d:].count('/-') == before[d:].count('-/'):
            doc = before[d:] + '\n'
    return doc + text[a:b]


def notice(origin):
    return (HEADER + '\n/-\nModified for the independent Lax packaging by Édouard Bonnet, 2026.\n'
            f'Derived from 3sum-apsp/{origin} at upstream commit {PIN}.\n'
            'Changes: Lax module/namespace layout, separated concepts and proofs, archive\n'
            'annotations, and compatibility with the archive Lean/mathlib environment.\n'
            'See NOTICE and README.md in the submission root for provenance and scope.\n-/\n')


def write(path, text):
    if not path.exists() or path.read_text() != text:
        if CHECK:
            raise SystemExit(f'Generated source differs: {path.relative_to(ROOT)}')
        path.write_text(text)


END_MODULES = {
    **dict.fromkeys(['Instr', 'exec', 'loadWords'], 'WordRAM'),
    **dict.fromkeys(['BigO', 'Problem', 'rowByRow'], 'PolynomialTime'),
    **dict.fromkeys(['ExactTriangle', 'ε_T', 'Theorem_19'], 'ExactTriangle'),
    **dict.fromkeys(['ThreeSum', 'Theorem_22_3SUM'], 'ThreeSUM'),
    **dict.fromkeys(['MinPlusProduct', 'Theorem_22_MinPlus'], 'MinPlusProduct'),
    **dict.fromkeys(['Path', 'APSP', 'Theorem_22_APSP'], 'APSP'),
    **dict.fromkeys(['ZeroWeightKClique', 'Corollary_39_ZeroWeight'], 'ZeroWeightClique'),
}


def core_refs(text):
    return re.sub(r'EndStatement\.([\w]+)', lambda m: f'{C}.{END_MODULES[m[1]]}.{m[1]}', text)


concepts = []
targets = {}


def concept(name, title, description, imports, code, claims=(), math=True, opens=()):
    path = ROOT / 'concepts' / C / (name + '.lean')
    path.parent.mkdir(parents=True, exist_ok=True)
    imp = (MATH + '\n' if math else '') + ''.join(f'import {C}.{x}\n' for x in imports)
    opening = ('open Finset\n' if math else '') + ''.join(f'open {C}.{x}\n' for x in opens)
    annotation = f'/-!\n---\ntitle: {title}\ntype: {"theorem" if claims else "definition"}\n---\n{description}\n-/\n'
    body = core_refs(code)
    for statement, proof in claims:
        body += f'\n\n/-- {title}: {statement.replace("_", " ")}. -/\naxiom {proof} : {statement}\n'
        targets[statement] = (name, proof)
    text = notice('EndStatement.lean / PaperStatements.lean') + '\n' + imp + '\n' + annotation
    text += f'\nnamespace {C}.{name}\n\n' + opening + '\n' + body.strip() + f'\n\nend {C}.{name}\n'
    write(path, text)
    concepts.append(name)


def ds(source, names):
    return '\n\n'.join(decl(source, n) for n in names.split())


concept('WordRAM', 'A word RAM with signed addresses',
    'A deterministic random-access machine with $W$-bit words, signed integer addresses, '
    'modular addition, subtraction and multiplication, indirect loads and stores, a negative-word '
    'branch, and acceptance or rejection. Every instruction costs one step. The initial memory '
    'contains the input followed by zeros; all negative addresses initially contain zero. '
    'The only literal instruction writes the constant $1$.', [],
    ds(END, 'Instr exec loadWords'), math=False)
concept('PolynomialTime', 'Uniform polynomial time on the word RAM',
    'For each fixed input-magnitude exponent $\\kappa$, one program, one word-size coefficient '
    'and one time bound work for every input size and every admissible word size. '
    'The input integers have absolute value at most $n^\\kappa$ and the words have at least '
    '$b(\\lfloor\\log_2 n\\rfloor+1)$ bits. The verdict and the output cells must both be correct. '
    'Rational exponents are expressed using integer powers.', ['WordRAM'],
    ds(END, 'BigO Problem Problem.SolvedBy Problem.SolvedInTime rowByRow'), math=False,
    opens=['WordRAM'])
for name, title, desc, names, claim in [
    ('ExactTriangle', 'Truly subcubic Exact Triangle',
     'Exact Triangle on a complete tripartite graph with $n$ vertices in each part and '
     'polynomially bounded integer weights is decidable deterministically in '
     '$O(n^{2.9983})$ word-RAM steps (Theorem 19). A triangle is accepted exactly when '
     'its three edge weights sum to zero.', 'ExactTriangle ε_T Theorem_19', 'Theorem_19'),
    ('ThreeSUM', 'Truly subquadratic 3SUM',
     'Given $n$ polynomially bounded integers, a deterministic word-RAM program decides '
     'whether three distinct positions contain numbers summing to zero in '
     '$O(n^{1.9992})$ steps (Theorem 22, using Corollary 26).',
     'ThreeSum Theorem_22_3SUM', 'Theorem_22_3SUM'),
    ('MinPlusProduct', 'Truly subcubic min-plus matrix multiplication',
     'The min-plus product of two $n\\times n$ matrices with polynomially bounded integer '
     'entries can be computed deterministically in $O(n^{2.99942})$ word-RAM steps '
     '(Theorem 22). The output contains the minimum of $A_{ik}+B_{kj}$ for each pair $(i,j)$.',
     'MinPlusProduct Theorem_22_MinPlus', 'Theorem_22_MinPlus'),
    ('APSP', 'Truly subcubic all-pairs shortest paths',
     'All-pairs shortest paths in a directed graph with $n$ vertices, polynomially bounded '
     'integer edge weights and no negative cycles can be computed deterministically in '
     '$O(n^{2.99942})$ word-RAM steps (Theorem 22). Each output pair contains a reachability '
     'flag and, when reachable, the minimum weight of a path. Paths may repeat vertices.',
     'Path APSP Theorem_22_APSP', 'Theorem_22_APSP'),
    ('ZeroWeightClique', 'Faster zero-weight k-clique',
     'For every fixed $k\\geq 3$, a zero-weight clique with one vertex in each of $k$ parts '
     'of size $n$ is decidable deterministically in '
     '$O(n^{k-0.0017\\lfloor k/3\\rfloor})$ word-RAM steps. Edge weights are '
     'polynomially bounded integers (Corollary 39).',
     'ZeroWeightKClique Corollary_39_ZeroWeight', 'Corollary_39_ZeroWeight'),
]:
    deps = ['PolynomialTime'] + (['ExactTriangle'] if name == 'ZeroWeightClique' else [])
    concept(name, title, desc, deps, ds(END, names), [(claim, 'algorithm')], math=False,
            opens=deps)

concept('RAMResources', 'Time bounds, persistent queries and phased inputs',
    'The word-RAM resource conventions for problems with several size parameters, real '
    'exponents, logarithmic factors, persistent data structures and inputs revealed in phases. '
    'Programs are fixed before the instance. Queries retain the memory left by earlier queries; '
    'a phase cannot inspect the input of a later phase.', ['PolynomialTime'],
    ds(PAPER, 'Admissible output Problem Solves SolvesWithin SolvedInTimeAt SolvedInTime '
       'SolvedInPolylogTime SolvedInLittleOTime withQuery Serves withInput RunsPhases Within'),
    opens=['WordRAM'])
concept('ThinMatrices', 'Thin matrix products and persistent entry queries',
    'Two integer matrices have dimensions $N\\times D$ and $D\\times N$, and entries '
    'bounded in absolute value by $U$. Wanted output positions are a list without repetitions. '
    'The data-structure specification bounds preprocessing time and the extent of retained '
    'memory, then requires correctness for every finite sequence of entry queries.',
    ['RAMResources'], ds(PAPER, 'rowMajor bit ThinPair ThinInstance ThinInstance.input thinProduct '
        'ThinPair.input IsDataStructure'), opens=['WordRAM', 'RAMResources'])
concept('LopsidedTriangles', 'Lopsided all-edges triangle detection and counting',
    'An unweighted tripartite graph has two parts of size $N$, a middle part of size at most '
    '$D$, and a specified set of query edges between the large parts. The tasks are to detect '
    'or count the triangles containing each query edge. The input uses two Boolean '
    'biadjacency matrices; zero padding represents a smaller middle part.', ['ThinMatrices'],
    ds(PAPER, 'LopInstance') + '\n\nattribute [instance] LopInstance.fintypeM\n\n' +
    ds(PAPER, 'LopInstance.MiddleAtMost LopInstance.commonNeighbors LopInstance.InTriangle '
       'LopInstance.numTriangles LopInstance.IsDetectionAnswer LopInstance.ofMatrices') +
    f'\n\nabbrev ThinInstance := {C}.ThinMatrices.ThinInstance\n\n' +
    ds(PAPER, 'ThinInstance.ZeroOne ThinInstance.lop lopCount lopDetect'),
    opens=['WordRAM', 'RAMResources', 'ThinMatrices'])
concept('MatrixParameters', 'Exponents for thin matrix preprocessing',
    'The entropy expression and parameter functions governing the preprocessing/query '
    'trade-off in Section 4. The threshold is '
    '$\\varepsilon^*=\\log 4/(5\\log 10)>0.1204$. The cost expressions retain the '
    'paper’s integer recursion parameters and logarithmic factors.', [],
    ds(PAPER, 'N0 K alpha rho cost8 costQuery cost9 entropy lnΛ Rc epsStar rhoC gammaOf qOf'))
concept('CliqueOptimization', 'Minimum- and maximum-weight multipartite cliques',
    'For fixed $k$, output the vertices of a minimum- or maximum-weight clique with one '
    'vertex from each of $k$ parts of size $n$. The encoding contains all $k^2$ blocks; '
    'the objective sums only the edges with part indices $i<j$.', ['ZeroWeightClique'],
    ds(PAPER, 'cliqueWeight MinKClique MaxKClique'))
concept('HintedMatrixVector', 'Hinted Boolean matrix-vector problems',
    'The v-hinted Mv, Mv-hinted Mv and uMv-hinted uMv problems reveal their inputs in '
    'successive phases. This specification includes the Boolean products, phase layouts and '
    'the conjectured trade-offs. Rectangular matrix-multiplication exponents are numerical '
    'parameters here; their values and lower bounds are not asserted.', ['ThinMatrices'],
    'namespace HintedMv\n\n' + ds(PAPER, 'boolMul toInt vHintedOutput MvHintedOutput '
      'uMvHintedOutput Conjecture52 Conjecture57 Conjecture512') + '\n\nend HintedMv\n\nopen HintedMv\n\n' +
    ds(PAPER, 'hintSize AchievesVHinted AchievesMvHinted AchievesUMvHinted'),
    opens=['WordRAM', 'RAMResources', 'ThinMatrices'])
concept('MatrixTradeoffs', 'Thin matrix preprocessing and query trade-offs',
    'Theorem 24 and Corollary 31 give preprocessing time/space and per-entry query bounds. '
    'For every $\\varepsilon<\\varepsilon^*$ and $q>0$, some $\\gamma>0$ permits '
    '$O(N^2\\log^2 D/D^\\gamma)$ preprocessing and $O(D^q\\log D)$ queries when '
    '$2\\leq D\\leq N^\\varepsilon$. Corollary 31 supplies explicit parameter choices.',
    ['ThinMatrices', 'MatrixParameters'],
    ds(PAPER, 'thinDom HasDataStructure Theorem_24 Corollary_31 DataStructureBelow'),
    [('Theorem_24', 'theorem24'), ('Corollary_31', 'corollary31')],
    opens=['WordRAM', 'RAMResources', 'ThinMatrices', 'MatrixParameters'])
concept('MatrixPreprocessing', 'Explicit thin matrix preprocessing bounds',
    'Corollary 26 gives $O(N^2/D^{0.063})$ preprocessing time and space and '
    '$O(D^{0.437})$ time per query for $1\\leq D$ and $D^{18}\\leq N$. Theorem 30 '
    'gives the underlying bounds at integer recursion parameters. Theorem 3 extends '
    'the trade-off to every $\\varepsilon<0.1204$ and every positive query exponent.',
    ['MatrixTradeoffs'], ds(PAPER, 'Corollary_26 theorem30Dom Theorem_30 Theorem_3'),
    [('Corollary_26', 'corollary26'), ('Theorem_30', 'theorem30'), ('Theorem_3', 'theorem3')],
    opens=['WordRAM', 'RAMResources', 'ThinMatrices', 'MatrixParameters', 'MatrixTradeoffs'])
concept('SparseMatrixProduct', 'Faster computation of selected matrix-product entries',
    'Theorem 1 computes up to $N^2/\\sqrt D$ selected entries in '
    '$O(N^2/D^{0.063})$ time when $1\\leq D$ and $D^{18}\\leq N$. More generally, '
    'for $D\\leq N^\\varepsilon$, $\\varepsilon<0.1204$, any $N^2/D^\\kappa$ '
    'selected entries admit a polynomial saving for every $\\kappa>0$. The individual '
    'statements also record Theorems 5, 25 and 30 and Corollaries 26 and 32.',
    ['MatrixPreprocessing'], ds(PAPER, 'Theorem_5 Theorem_25 Corollary_26_wanted '
        'Theorem_30_wanted Corollary_32 WantedBelow Theorem_1'),
    [(n, p) for n,p in [('Theorem_5','theorem5'), ('Theorem_25','theorem25'),
     ('Corollary_26_wanted','corollary26_wanted'), ('Theorem_30_wanted','theorem30_wanted'),
     ('Corollary_32','corollary32'), ('Theorem_1','theorem1')]],
    opens=['WordRAM', 'RAMResources', 'ThinMatrices', 'MatrixParameters', 'MatrixTradeoffs', 'MatrixPreprocessing'])
concept('LopsidedTriangleAlgorithms', 'Faster lopsided triangle algorithms',
    'Corollary 16 solves counting and detection in '
    '$O(|W|D^{0.437}+N^2/D^{0.063})$ time for $1\\leq D$ and $D^{18}\\leq N$. '
    'Corollary 15 records the earlier logarithmic bound for powers of four.',
    ['LopsidedTriangles'], ds(PAPER, 'Corollary_15 Corollary_16'),
    [('Corollary_15','corollary15'), ('Corollary_16','corollary16')],
    opens=['WordRAM','RAMResources','ThinMatrices','LopsidedTriangles'])
concept('IntegerAlgorithmBounds', 'Integer algorithms before rounding the exponents',
    'Theorem 19 gives Exact Triangle bounds from both constructions. Theorem 22 carries '
    'these improvements to 3SUM, min-plus product and APSP, retaining the logarithmic and '
    '$o(1)$ factors before rounding. These statements are deterministic integer word-RAM '
    'bounds; they do not assert the paper’s real-RAM or randomized bounds.',
    ['ExactTriangle','ThreeSUM','MinPlusProduct','APSP','RAMResources'],
    ds(PAPER, 'Theorem_19 Theorem_22_first Theorem_22_second Theorem_22_threeSum Theorem_2'),
    [('Theorem_19','theorem19'), ('Theorem_22_first','theorem22_first'),
     ('Theorem_22_second','theorem22_second'), ('Theorem_22_threeSum','theorem22_threeSum'),
     ('Theorem_2','theorem2')], opens=['WordRAM','RAMResources'])
concept('WeightedCliqueAlgorithms', 'Faster weighted clique algorithms',
    'Corollary 39 gives deterministic time '
    '$O(n^{k-0.0017\\lfloor k/3\\rfloor})$ for zero-weight clique detection and for '
    'finding a minimum- or maximum-weight clique, for every fixed $k\\geq3$ and '
    'polynomially bounded integer weights.', ['ZeroWeightClique','CliqueOptimization','RAMResources'],
    ds(PAPER, 'Corollary_39_zero Corollary_39_min_max'),
    [('Corollary_39_zero','zeroWeight'), ('Corollary_39_min_max','minMax')],
    opens=['WordRAM','RAMResources','CliqueOptimization'])
concept('HintedAlgorithms', 'Improved algorithms with thin hints',
    'Corollary 40 supplies explicit and general phase-time savings for the three hinted '
    'Boolean matrix-vector problems. Theorem 4 contradicts their conjectured trade-offs '
    'in the stated thin-hint regimes, conditional on the displayed numerical lower bounds '
    'for rectangular multiplication exponents. Those lower bounds are hypotheses, '
    'not independently verified facts about matrix-multiplication exponents.',
    ['HintedMatrixVector','MatrixParameters'], ds(PAPER, 'Corollary_40_times '
        'Corollary_40_general_times Corollary_40_fail Theorem_4'),
    [('Corollary_40_times','explicitTimes'), ('Corollary_40_general_times','generalTimes'),
     ('Theorem_4','theorem4')], opens=['WordRAM','RAMResources','ThinMatrices','HintedMatrixVector','MatrixParameters'])

write(ROOT / 'concepts' / (C + '.lean'), ''.join(f'import {C}.{x}\n' for x in sorted(concepts)))


def adapt(text, origin, extra_imports=()):
    # Adapt upstream module visibility; all proof declarations gain namespace P.
    text = text[text.index('-/') + 2:].lstrip()
    if text.startswith('module\n'):
        text = text[len('module\n'):].lstrip()
    imports = []
    lines = text.splitlines()
    while lines and (not lines[0].strip() or re.match(r'(public )?import ', lines[0])):
        line = lines.pop(0)
        if not line.strip():
            continue
        mod = line.split()[-1]
        if mod == 'EndStatement':
            mod = P + '.UpstreamEndStatement'
        elif mod == 'PaperStatements':
            mod = P + '.UpstreamPaperStatements'
        elif mod.startswith('ThreeSumApsp'):
            mod = P + '.' + mod
        imports.append('import ' + mod)
    imports += ['import ' + x for x in extra_imports]
    body = '\n'.join(lines)
    body = body.replace('@[expose] ', '').replace('public section', 'section')
    body = body.replace('_root_.Light', f'_root_.{P}.Light').replace('_root_.ThreeSumApsp', f'_root_.{P}.ThreeSumApsp')
    body = body.replace('S.card_filter_div_eq_le', '(Finset.card_filter_div_eq_le S)')
    body = body.replace('Finset.univ.card_filter_div_eq_le', '(Finset.card_filter_div_eq_le Finset.univ)')
    # Mathlib namespace extensions must retain access to the root namespace.
    for ns in ['Finset', 'Nat', 'Int', 'Real', 'List']:
        body = re.sub(r'(?m)^namespace ' + ns + r'$', 'namespace ' + ns + '\n\nopen _root_.' + ns, body)
        body = re.sub(r'(?m)^open ([^\n]+)',
                      lambda m: 'open ' + re.sub(r'(?<![\w.])' + ns + r'(?=\s|$)',
                                                ns + ' _root_.' + ns, m[1]), body)
    scopes = []
    for m in re.finditer(r'(?m)^(namespace|(?:noncomputable )?section|end)(?: ([\w.]+))?\s*$', mask_comments(body)):
        if m[1] == 'end':
            for _ in (m[2] or '').split('.'):
                if scopes:
                    scopes.pop()
        elif m[1] == 'namespace':
            scopes.extend(m[2].split('.'))
        else:
            scopes.append(m[2] or '')
    closing = ''.join('\nend' + (' ' + scope if scope else '') for scope in reversed(scopes))
    return notice(origin) + '\n' + '\n'.join(imports) + f'\n\nnamespace {P}\n\n' + body.rstrip() + closing + f'\n\nend {P}\n'


def replace_decl(text, name, replacement):
    a, b = decl_span(text, name)
    prefix = text[:a]
    if replacement.startswith('export ') and prefix.rstrip().endswith('-/'):
        doc = prefix.rfind('/--')
        if doc >= 0:
            prefix = prefix[:doc] + prefix[doc:].replace('/--', '/-', 1)
    return prefix + replacement + text[b:]


end_proof = replace_decl(END, 'Instr', f'export {C}.WordRAM (Instr)')
end_proof = replace_decl(end_proof, 'exec', f'export {C}.WordRAM (exec)')
end_proof = replace_decl(end_proof, 'Path', f'abbrev Path := @{C}.APSP.Path')
proof_dir = ROOT / 'proofs' / P
proof_dir.mkdir(parents=True, exist_ok=True)
write(proof_dir / 'UpstreamEndStatement.lean', adapt(end_proof, 'EndStatement.lean', [C+'.WordRAM', C+'.APSP']))
paper_proof = replace_decl(PAPER, 'ThinPair', f'abbrev ThinPair := {C}.ThinMatrices.ThinPair')
paper_proof = replace_decl(paper_proof, 'ThinInstance', f'abbrev ThinInstance := {C}.ThinMatrices.ThinInstance')
for shared in ['Serves', 'RunsPhases']:
    paper_proof = replace_decl(paper_proof, shared, f'export {C}.RAMResources ({shared})')
write(proof_dir / 'UpstreamPaperStatements.lean', adapt(paper_proof, 'PaperStatements.lean', [C+'.ThinMatrices']))
upstream_files = {'.'.join(p.relative_to(UP).with_suffix('').parts): p
                  for p in (UP / 'ThreeSumApsp').rglob('*.lean')}
reachable = set()
pending = ['ThreeSumApsp.RunningTimes', 'ThreeSumApsp.Statements.Exponents']
while pending:
    mod = pending.pop()
    if mod in reachable:
        continue
    reachable.add(mod)
    pending.extend(m for m in re.findall(r'^(?:public )?import (\S+)',
                   upstream_files[mod].read_text(), re.M) if m in upstream_files)
for mod, source in sorted(upstream_files.items()):
    rel = source.relative_to(UP)
    dest = proof_dir / rel
    if mod not in reachable:
        if dest.exists():
            if CHECK:
                raise SystemExit(f'Unneeded generated source: {dest.relative_to(ROOT)}')
            dest.unlink()
        continue
    dest.parent.mkdir(parents=True, exist_ok=True)
    write(dest, adapt(source.read_text(), str(rel)))

# Initial certificates use the original proofs. The dependency refinement below is
# deliberately limited to actual theorem applications, never decorative graph edges.
certificates = []
proof_sources = {p: p.read_text() for p in (UP / 'ThreeSumApsp').rglob('*.lean')}
named_assumptions = {
    'wordRam_' + statement[0].lower() + statement[1:]:
        f'(show Items.{statement} from {C}.{module}.{axiom})'
    for statement, (module, axiom) in targets.items()
    if module not in {'ExactTriangle', 'ThreeSUM', 'MinPlusProduct', 'APSP', 'ZeroWeightClique'}
}


def certificate_body(proof):
    # Expose genuine direct uses of other certified machine-level statements.
    # Procedure-level reductions remain fully proved inside the upstream library.
    if proof.startswith('endStatement_') or proof in {'wordRam_theorem_1', 'wordRam_theorem_2',
                                                     'wordRam_theorem_3', 'wordRam_theorem_4'}:
        for text in proof_sources.values():
            if re.search(r'(?m)^theorem ' + re.escape(proof) + r'\s*:', text):
                a, b = decl_span(text, proof)
                body = text[a:b].split(':=', 1)[1].strip()
                for original, assumed in named_assumptions.items():
                    body = re.sub(r'\b' + re.escape(original) + r'\b', lambda _: assumed, body)
                return body
        raise ValueError(proof)
    return proof
core_claims = [
    ('ExactTriangle', 'Theorem_19', 'endStatement_theorem_19'),
    ('ThreeSUM', 'Theorem_22_3SUM', 'endStatement_theorem_22_3SUM'),
    ('MinPlusProduct', 'Theorem_22_MinPlus', 'endStatement_theorem_22_MinPlus'),
    ('APSP', 'Theorem_22_APSP', 'endStatement_theorem_22_APSP'),
    ('ZeroWeightClique', 'Corollary_39_ZeroWeight', 'endStatement_corollary_39_zeroWeight'),
]
for module, statement, proof in core_claims:
    certificates.append(f'/--\n---\nconclusion: {C}.{module}.algorithm\n---\nThe upstream conversion from the certified real-exponent bound to the rational-exponent formulation, preserving the program and input/output semantics.\n-/\ntheorem lax_{proof} : {C}.{module}.{statement} :=\n  {certificate_body(proof)}')
for statement, (module, axiom) in targets.items():
    if statement in {x[1] for x in core_claims} and module != 'IntegerAlgorithmBounds':
        continue
    proof = 'wordRam_' + statement[0].lower() + statement[1:]
    certificates.append(f'/--\n---\nconclusion: {C}.{module}.{axiom}\n---\nThe corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.\n-/\ntheorem lax_{proof} : {C}.{module}.{statement} :=\n  {certificate_body(proof)}')
cert = 'import '+C+'\nimport '+P+'.ThreeSumApsp.Statements.Exponents\nimport '+P+'.ThreeSumApsp.RunningTimes\n\n'
cert += f'namespace {P}.ThreeSumApsp\n\nopen WordRam\n\n' + '\n\n'.join(certificates) + f'\n\nend {P}.ThreeSumApsp\n'
write(proof_dir / 'Certificates.lean', notice('ThreeSumApsp/Statements and RunningTimes') + '\n' + cert)
modules = sorted('.'.join(path.relative_to(ROOT / 'proofs').with_suffix('').parts) for path in proof_dir.rglob('*.lean'))
write(ROOT / 'proofs' / (P + '.lean'), ''.join(f'import {mod}\n' for mod in modules))
write(ROOT / 'LICENSE', (UP / 'LICENSE').read_text())
write(ROOT / 'NOTICE', (UP / 'NOTICE').read_text())
print(f'{"Verified" if CHECK else "Generated"} {len(concepts)} concepts, {len(certificates)} certificates and {len(modules)} proof modules.')
