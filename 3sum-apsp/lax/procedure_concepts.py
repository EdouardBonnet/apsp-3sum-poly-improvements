"""Expose the upstream callable contracts, without importing proof modules.

Copyright 2026 Édouard Bonnet. SPDX-License-Identifier: Apache-2.0
"""
import re

# Source theorem, concept, statement name, exact upstream proposition.
CALLABLES = [
    ('Light.Sec2.claim_theorem_5', 'SparseMatrixProduct', 'callableTheorem5',
     'Claim.Theorem_5 lightModel'),
    ('Light.Sec4.claim_corollary_26_wanted', 'MatrixPreprocessing', 'callableCorollary26',
     'Claim.Corollary_26_wanted lightModel'),
    *[(f'Light.Sec3.claim_{source}', 'LopsidedTriangleAlgorithms', target, f'Claim.{claim} lightModel')
      for source, target, claim in [
          ('corollary_15_first', 'callableCorollary15First', 'Corollary_15_first'),
          ('corollary_15', 'callableCorollary15General', 'Corollary_15_general'),
          ('corollary_16', 'callableCorollary16', 'Corollary_16')]],
    *[(f'Light.Sec3.claim_{source}', 'IntegerAlgorithmBounds', target,
       f'Claim.{claim} lightModel {delta} {power}')
      for source, target, claim, delta, power in [
          ('theorem_19_usingTheorem5', 'callableExactTriangleFirst', 'Theorem_19_explicit', '(1 / 648)', 2),
          ('theorem_19_usingCorollary26', 'callableExactTriangleSecond', 'Theorem_19_explicit', '0.00175', 1),
          ('exactTriangleUniform_usingTheorem5', 'uniformExactTriangleFirst', 'ExactTriangleUniform', '(1 / 648)', 2),
          ('exactTriangleUniform_usingCorollary26', 'uniformExactTriangleSecond', 'ExactTriangleUniform', '0.00175', 1)]],
    *[(f'Light.Sec3.claim_{source}', 'AlgorithmReductions', target, f'Claim.{claim} lightModel{params}')
      for source, target, claim, params in [
          ('theorem_17₅', 'exactTriangleViaTheorem5', 'Theorem_17', ' strassen paramD₅ paramG₅'),
          ('theorem_17₂₆', 'exactTriangleViaCorollary26', 'Theorem_17', ' strassen paramD₂₆ paramG₂₆'),
          ('theorem_21a', 'threeSumFromExactTriangle', 'Theorem_21a', ''),
          ('theorem_21b_minPlus', 'minPlusFromExactTriangle', 'Theorem_21b_minPlus', ''),
          ('theorem_21b_apsp', 'apspFromExactTriangle', 'Theorem_21b_apsp', ''),
          ('lopCountFromThinProduct', 'triangleCountsFromMatrixProduct', 'LopCountFromThinProduct', ''),
          ('lopDetectFromCount', 'triangleDetectionFromCounts', 'LopDetectFromCount', ''),
          ('lopSplit', 'splitTriangleQueries', 'LopSplit', '')]],
]


def generate(up, paper, concept, ds, decl, mask_comments, prefix):
    """Create definition concepts and return replacements sharing nominal types.

    Every definition is copied from the pinned upstream. The proof library
    re-exports shared types so these are the *same* program semantics and tasks,
    not abstract predicates standing in for the algorithms.
    """
    sharing = {}

    def source(path):
        return (up / path).read_text().replace('@[expose] ', '')

    def share(path, module, names):
        text = source(path)
        replacements = sharing.setdefault(path, [])
        for name in names.split():
            code = decl(text, name)
            exported = [name]
            masked = mask_comments(code)
            if re.search(r'(?m)^structure ', masked):
                exported += [name + '.mk']
                exported += [name + '.' + field for field in
                             re.findall(r'^  (\w+)\s*:', masked, re.M)]
            if re.search(r'(?m)^inductive ', masked):
                # Constructor alternatives on the same line occur for Op.
                exported += [name + '.' + ctor for ctor in
                             re.findall(r'\|\s*(\w+)', masked)]
            replacement = f'export {prefix}.{module} ({" ".join(exported)})'
            replacements.append((name, replacement))

    syntax_path = 'ThreeSumApsp/Lang/Syntax.lean'
    syntax_names = ('Op Op.eval Expr Cond Stmt Program State Limits Expr.val Expr.cost '
                    'Limits.Addr Expr.Safe Cond.Holds Cond.cost Cond.Safe frame memOf Exec State.Bounded')
    concept('StructuredPrograms', 'Structured programs and exact execution costs',
            'The imperative language used to construct the algorithms: finite programs, '
            'procedure calls, memory, word and stack limits, and an exact step-counted '
            'execution relation. The upstream compiler proves that these programs run on '
            'the word RAM with constant-factor overhead.', [], ds(source(syntax_path), syntax_names),
            origin=syntax_path)
    share(syntax_path, 'StructuredPrograms', syntax_names)

    contract_parts = [
        ('ThreeSumApsp/Lang/Logic.lean', 'Ends'),
        ('ThreeSumApsp/Lang/WordSize.lean', 'polyBound'),
        ('ThreeSumApsp/Lang/Regions.lean', 'Inside Outside Apart SameOn Kept KeptBut'),
        ('ThreeSumApsp/Lang/Lib/Seg.lean', 'Seg SegN'),
        ('ThreeSumApsp/Util/List.lean', 'AbsLe'),
        ('ThreeSumApsp/Lang/Tasks.lean', 'Need Need.Ok PolyNeed Task Solves SolvedIn TaskN SolvesN PolyNeedN'),
    ]
    concept('ProcedureContracts', 'Reusable procedures and memory preservation',
            'A solver remains correct when other procedures are appended to its program. '
            'Its contract specifies inputs, outputs, preserved memory, time, and polynomial '
            'bounds on words, scratch space and call depth. These guarantees make the '
            'algorithmic reductions compositional.', ['StructuredPrograms'],
            '\n\n'.join(ds(source(path), names) for path, names in contract_parts),
            opens=['StructuredPrograms'], origin='ThreeSumApsp/Lang and Util/List.lean')
    for path, names in contract_parts:
        share(path, 'ProcedureContracts', names)

    problems_path = 'ThreeSumApsp/Programs/Tasks.lean'
    problem_names = ('TriInst TriInst.Pre etTask ntTask VecInst VecInst.Pre c3Task s3Task '
                     'MatInst MatInst.Pre mpTask GraphInst GraphInst.Pre apTask ThinInst ThinInst.Pre '
                     'ThinInst.ZeroOne thinEntry thinOut thinTask lopCountTask lopDetectTask ThinSolvedIn LopSolvedIn')
    problems = ds(paper, 'TriangleInstance')
    problems += '\n\nnamespace TriangleInstance\n\n' + ds(paper, 'S IsZeroTriangle HasZeroTriangle')
    problems += '\n\nend TriangleInstance\n\n'
    problems += ds(paper, 'TriangleInstance.HasNegativeTriangle Convolution3SUM walkEnd walkWeight NoNegativeCycle IsDistanceMatrix')
    problems += f'\n\nabbrev ThreeSum := @{prefix}.ThreeSUM.ThreeSum.yes\n\n'
    problems += ds(source('ThreeSumApsp/Spec/Sec3/Problems.lean'),
                   'entry vecOf triOf graphOf minPlusEntry minPlusList')
    problems += '\n\nopen Classical in\n' + decl(source('ThreeSumApsp/Util/Flag.lean'), 'flag')
    problems += '\n\n' + ds(source(problems_path), problem_names)
    concept('CallableProblems', 'Calling conventions for matrix and graph algorithms',
            'Concrete memory layouts and input/output contracts for thin matrix products, '
            'lopsided triangle counting and detection, Exact and Negative Triangle, '
            '3SUM, min-plus products, and APSP. Solvers preserve the caller’s other memory '
            'and may be reused on successive inputs.', ['ProcedureContracts', 'ThreeSUM'], problems,
            opens=['StructuredPrograms', 'ProcedureContracts'],
            origin='PaperStatements.lean / ThreeSumApsp/Programs/Tasks.lean / Spec/Sec3/Problems.lean')
    share(problems_path, 'CallableProblems',
          'TriInst TriInst.Pre VecInst VecInst.Pre MatInst MatInst.Pre GraphInst GraphInst.Pre ThinInst ThinInst.Pre')
    share('PaperStatements.lean', 'CallableProblems', 'TriangleInstance walkEnd walkWeight')
    share('PaperStatements.lean', 'CallableProblems.TriangleInstance', 'S IsZeroTriangle HasZeroTriangle')
    share('PaperStatements.lean', 'CallableProblems',
          'TriangleInstance.HasNegativeTriangle Convolution3SUM NoNegativeCycle IsDistanceMatrix')

    params = ds(paper, 'queryCap IsPowLittleO IsPowPolylog IsBigOPow')
    for path, names in [
        ('ThreeSumApsp/Util/Log.lean', 'logU'),
        ('ThreeSumApsp/Util/Ceil.lean', 'cbrtCeil'),
        ('ThreeSumApsp/Sec3/Parameters.lean',
         'DivNondecreasing GoodTime uniformTime termScans termPrime termBuild strassen paramD₅ paramG₅ paramD₂₆ paramG₂₆ splitCap'),
        ('ThreeSumApsp/Util/Asymptotics/UpperBounds.lean', 'UpperBigOPow UpperPowPolylog UpperPowLittleO'),
    ]:
        params += '\n\n' + ds(source(path), names)
    claims_path = 'ThreeSumApsp/TimeClaims/Sec3/Definitions.lean'
    claims = source(claims_path).split('namespace ThreeSumApsp\n', 1)[1].rsplit('end ThreeSumApsp', 1)[0]
    claims = claims.replace('/-!', '/-')
    model = decl(source('ThreeSumApsp/Programs/LightModel.lean'), 'lightModel')
    concept('CallableAlgorithms', 'Time bounds for callable algorithms and reductions',
            'Running-time statements interpreted by actual procedures with the preceding '
            'memory and resource contracts. A reduction converts any solver satisfying its '
            'input contract into a solver for its output problem, charging all calls and '
            'overhead. The model is a definition, not an assumed machine oracle.',
            ['CallableProblems'], 'open Filter Asymptotics\n\n' + params + '\n\n' + claims + '\n\n' + model,
            opens=['StructuredPrograms', 'ProcedureContracts', 'CallableProblems'],
            origin='ThreeSumApsp/TimeClaims/Sec3/Definitions.lean / Programs/LightModel.lean / Sec3/Parameters.lean')
    share(claims_path, 'CallableAlgorithms', 'DetTimeModel')

    concept('AlgorithmReductions', 'Callable reductions between the algorithmic problems',
            'Theorem 17 reduces Exact Triangle to lopsided triangle detection at the two '
            'parameter choices used in the paper. Theorem 21 transfers an Exact Triangle '
            'solver to 3SUM, min-plus products and APSP. Additional reductions turn selected '
            'matrix entries into triangle counts and detection, and split large query sets. '
            'All are proved transformations of callable programs.', [], '')
    return sharing


SHARED_NAMESPACES = {
    **dict.fromkeys(['Light.' + x for x in ['Op', 'Expr', 'Cond', 'Stmt', 'State', 'Limits', 'Exec', 'Program']],
                    'StructuredPrograms'),
    **dict.fromkeys(['Light.' + x for x in [
        'Need', 'Task', 'TaskN', 'Ends', 'PolyNeed', 'Solves', 'SolvedIn', 'SolvesN', 'PolyNeedN',
        'Inside', 'Outside', 'Apart', 'SameOn', 'Kept', 'KeptBut', 'Seg', 'SegN']], 'ProcedureContracts'),
    'ThreeSumApsp.AbsLe': 'ProcedureContracts',
    **dict.fromkeys(['Light.' + x for x in ['TriInst', 'VecInst', 'MatInst', 'GraphInst', 'ThinInst']],
                    'CallableProblems'),
    'ThreeSumApsp.TriangleInstance': 'CallableProblems',
    'ThreeSumApsp.DetTimeModel': 'CallableAlgorithms',
}


def declarations(text, mask_comments):
    """Yield declaration names and ends with their enclosing namespaces."""
    masked = mask_comments(text)
    commands = list(re.finditer(
        r'(?m)^(?:(?:@\[[^\n]*\]|noncomputable|private|protected|unsafe|partial)\s+)*'
        r'(namespace|section|end|def|abbrev|structure|inductive|theorem|lemma|axiom|'
        r'open|export|attribute|set_option|variable|instance|infix[^ ]*|notation|syntax|macro)'
        r"(?:[ \t]+([\w.?!']+))?", masked))
    scopes = []
    for i, command in enumerate(commands):
        kind, name = command[1], command[2]
        if kind in {'namespace', 'section'}:
            if kind == 'namespace':
                scopes.extend(name.split('.'))
            else:
                scopes.append('')
        elif kind == 'end':
            for _ in (name or '').split('.'):
                if scopes:
                    scopes.pop()
        elif kind in {'def', 'abbrev', 'structure', 'inductive', 'theorem', 'lemma', 'axiom'}:
            full = name[7:] if name.startswith('_root_.') else '.'.join(
                [scope for scope in scopes if scope] + [name])
            next_start = commands[i + 1].start() if i + 1 < len(commands) else len(text)
            stop = len(masked[:next_start].rstrip())
            yield full, stop


def method_aliases(body, mask_comments, concept_names, concept_prefix, proof_prefix):
    """Preserve upstream dot notation on shared types without adding declarations.

    `export` installs a name-resolution alias only. All actual new definitions
    and lemmas remain in the proof namespace; concept files import no proofs.
    """
    additions = []
    for full, stop in declarations(body, mask_comments):
        full = full.removeprefix(proof_prefix + '.')
        for source, module in SHARED_NAMESPACES.items():
            if not full.startswith(source + '.'):
                continue
            target = concept_prefix + '.' + module + '.' + full.split('.', 1)[1]
            if target in concept_names:
                break
            parent, leaf = full.rsplit('.', 1)
            target_parent = target.rsplit('.', 1)[0]
            exported = f'«{leaf}»'
            if source == 'Light.ThinInst' and full.startswith(source + '.Pre.'):
                # Fully qualified declarations of these helpers do not register
                # ThinInst.Pre as a namespace. Export from the enclosing Light.
                parent = 'Light'
                target_parent = concept_prefix + '.' + module
                exported = f'ThinInst.Pre.«{leaf}»'
            additions.append((stop, f'\n\nwith_weak_namespace _root_.{target_parent} '
                              f'export _root_.{proof_prefix}.{parent} ({exported})'))
            break
    for stop, alias in reversed(additions):
        body = body[:stop] + alias + body[stop:]
    return body
