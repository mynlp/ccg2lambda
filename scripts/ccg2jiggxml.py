
from typing import Union, List, Optional, NamedTuple
from lxml import etree
import argparse
import subprocess
import tempfile
import sys
import re

Category = Union['Atomic', 'Functor']
Tree = Union['Node', 'Leaf']
Token = Union[str, 'Leaf']


test = """
(Sm
  (Sm.h
    (PPs.c *speaker*)
    (PPs\Sm.h
      (Sa.a
        (PPs.c *exp*)
        (PPs\Sa.h
          (<PPs\Sa>/<PPs\Sa>.a
            (NUM.c 二)
            (NUM\<<PPs\Sa>/<PPs\Sa>>.h 日)
          )
          (PPs\Sa.h
            (PPs\Sa.h つづけ)
            (<PPs\Sa>\<PPs\Sa>.a て)
          )
        )
      )
      (PPs\Sm.h
        (PPo1.c
          (NP.c 酒)
          (NP\PPo1.h を)
        )
        (PPo1\<PPs\Sm>.h
          (PPo1\<PPs\Sm>.h
            (PPo1\<PPs\Sm>.h
              (PPo1\<PPs\Sm>.h
                (PPo1\<PPs\Sm>.h 呑ん)
                (<PPo1\<PPs\Sm>>\<PPo1\<PPs\Sm>>.a だ)
              )
              (<PPo1\<PPs\Sm>>\<PPo1\<PPs\Sm>>.a の)
            )
            (<PPo1\<PPs\Sm>>\<PPo1\<PPs\Sm>>.a で)
          )
          (<PPo1\<PPs\Sm>>\<PPo1\<PPs\Sm>>.a ある)
        )
      )
    )
  )
  (Sm\Sm.a 。)
)"""


def find_closing_bracket(source: str) -> int:
    open_brackets = 0
    for i, c in enumerate(source):
        if c == '<':
            open_brackets += 1
        elif c == '>':
            open_brackets -= 1
        if open_brackets == 0:
            return i
    raise Exception("Mismatched brackets in string: " + source)


def drop_brackets(cat: str) -> str:
    if cat.startswith('<') and cat.endswith('>') \
            and find_closing_bracket(cat) == len(cat) - 1:
        return cat[1:-1]
    else:
        return cat


def find_non_nested_char(haystack: str, needles: str) -> int:
    open_brackets = 0
    for i, c in enumerate(haystack):
        if c == '<':
            open_brackets += 1
        elif c == '>':
            open_brackets -= 1
        elif open_brackets == 0:
            if c in needles:
                return i
    return -1


class Atomic(NamedTuple):
    string: str
    feature: Optional[str]

    def __str__(self) -> str:
        return self.to_string(bracket=False)

    @property
    def is_functor(self) -> bool:
        return False

    def to_string(self, bracket=False) -> str:
        if self.feature is not None:
            res = '{}[{}=true]'.format(self.string, self.feature)
        else:
            res = self.string
        return '(' + res + ')' if bracket else res


class Functor(NamedTuple):
    left: Category
    slash: str
    right: Category

    def __str__(self) -> str:
        return self.to_string(bracket=False)

    @property
    def is_functor(self) -> bool:
        return True

    def to_string(self, bracket=False) -> str:
        left = self.left.to_string(bracket=self.left.is_functor)
        right = self.right.to_string(bracket=self.right.is_functor)
        res = left + self.slash + right
        return '(' + res + ')' if bracket else res


def is_forward_application(cat1: Category, cat2: Category) -> bool:
    return cat1.is_functor and cat1.right == cat2


def is_backward_application(cat1: Category, cat2: Category) -> bool:
    return cat2.is_functor and cat2.right == cat1

def is_forward_composition(cat1: Category, cat2: Category) -> bool:
    return cat1.is_functor and cat2.is_functor and cat1.right == cat2.left


def is_backward_composition(cat1: Category, cat2: Category) -> bool:
    return cat1.is_functor and cat2.is_functor and cat1.right == cat2.left


def resolve_combinatory_rule(cat1: Category, cat2: Category) -> str:
    res = 'none'
    if is_forward_application(cat1, cat2):
        res = '>'
    elif is_backward_application(cat1, cat2):
        res = '<'
    elif is_forward_composition(cat1, cat2):
        res = '>B1'
    elif is_backward_composition(cat1, cat2):
        res = '<B1'
    return res


FEATURE_PATTERN = re.compile(r'[a-z]')


def parse_cat(cat: str) -> Category:
    """
    ex. PPo1\<PPs\Sm>.h --> PPo1\(PPs\Sm)
    """
    if len(cat) > 2 and cat[-2] == '.':
        cat = cat[:-2]
    cat = drop_brackets(cat)
    op_idx = find_non_nested_char(cat, '/\\')
    if op_idx == -1:
        feature_match = FEATURE_PATTERN.search(cat)
        if feature_match is not None:
            i = feature_match.start()
            cat, feature = cat[:i], cat[i:]
        else:
            feature = None
        return Atomic(cat, feature)
    else:
        left = parse_cat(cat[:op_idx])
        slash = cat[op_idx:op_idx + 1]
        right = parse_cat(cat[op_idx + 1:])
        return Functor(left, slash, right)


class Leaf(object):
    def __init__(self, cat: Category, word: str, position: int) -> None:
        self.cat = cat
        self.word = word
        self.position = position

    def __str__(self) -> str:
        return "({}, {})".format(self.cat, self.word)

    def __len__(self) -> int:
        return 1

    @property
    def start_of_span(self):
        return self.position

    @property
    def end_of_span(self):
        return self.position + 1

    @property
    def tokens(self) -> List[str]:
        return [self.word]

    @property
    def rule(self) -> str:
        return 'lex'


class Node(object):
    def __init__(self, cat: Category, children: List[Tree]) -> None:
        self.cat = cat
        self.children = children

    def __str__(self) -> str:
        return "({}, ({}))".format(self.cat, ", ".join(map(str, self.children)))

    def __len__(self) -> int:
        return sum(len(child) for child in self.children)

    @property
    def is_unary(self) -> bool:
        return len(self.children) == 1

    @property
    def left_child(self) -> Tree:
        return self.children[0]

    @property
    def right_child(self) -> Tree:
        if self.is_unary:
            raise RuntimeError('failed Tree.right_child: '
                               'node has only one child')
        return self.children[1]

    @property
    def start_of_span(self) -> int:
        return self.left_child.start_of_span

    @property
    def end_of_span(self):
        return self.start_of_span + len(self)

    @property
    def tokens(self) -> List[str]:
        return [token for child in self.children
                for token in child.tokens]

    @property
    def rule(self) -> str:
        if self.is_unary:
            return 'lex'
        else:
            return resolve_combinatory_rule(
                self.left_child.cat, self.right_child.cat)


def lexeme(line: str) -> List[Token]:
    def is_bracket(string: str) -> bool:
        return string in ['(', ')']

    process_leaf = False
    res = []
    position = 0
    line = line.replace('(', '( ').replace(')', ' )').split()
    for a, b in zip(line, line[1:]):
        if process_leaf:
            process_leaf = False
            continue
        process_leaf = not is_bracket(a) and not is_bracket(b)
        if process_leaf:
            res.append(Leaf(parse_cat(a), b, position))
            position += 1
        else:
            res.append(a)
    res.append(')')
    return res


class ABCTreeParser(object):
    def __init__(self, line: str) -> None:
        self.index = 0
        self.line = line
        self.items = lexeme(line)
        self.result = {}

    def next(self) -> Token:
        res = self.items[self.index]
        self.index += 1
        return res

    def peek(self) -> Token:
        return self.items[self.index]

    def peek_next(self) -> Token:
        return self.items[self.index+1]

    def peek_prev(self) -> Token:
        return self.items[self.index-1]

    def parse(self) -> Tree:
        """
        parse (IP-MAT (INTJ ..) (INTJ ..))
        """
        if isinstance(self.peek_next(), Leaf):
            res = self.parse_terminal()
        else:
            res = self.parse_non_terminal()
        return res

    def parse_terminal(self) -> Leaf:
        """
        parse ( INTJ えーっと )
        """
        assert self.next() == "("
        res = self.next()
        assert self.next() == ")"
        return res

    def parse_non_terminal(self) -> Node:
        """
        parse ( IP-MAT ( INTJ .. ) ( INTJ .. ) )
        """
        assert self.next() == '(', self.index
        tag = parse_cat(self.next())
        children = []
        while self.peek() != ')':
            children.append(self.parse())
        assert self.next() == ')'
        assert len(children) <= 2, 'Input tree must be binary'
        res = Node(tag, children)
        return res


def read_abc(filename: str, skip_ill_formed=False) -> List[Tree]:
    results = []
    for i, line in enumerate(open(filename)):
        try:
            tree = ABCTreeParser(line.strip()).parse()
            results.append(tree)
        except AssertionError as e:
            if skip_ill_formed:
                print(
                    'skipped parsing {}th sentence'.format(i),
                    file=sys.stderr)
            else:
                raise e
    return results


class ABCToXML(object):
    def __init__(self, sentence_id: int) -> None:
        self.sentence_id = sentence_id
        self._span_id = 0
        self.processed = 0

    @property
    def span_id(self) -> int:
        self._span_id += 1
        return self._span_id

    def process(self, tree: Tree) -> etree.Element:
        def traverse(node: Tree) -> str:
            index = 's{}_sp{}'.format(self.sentence_id, self.span_id)
            xml_node = etree.SubElement(res, 'span')
            xml_node.set('category', str(node.cat))
            xml_node.set('begin', str(node.start_of_span))
            xml_node.set('end', str(node.end_of_span))
            xml_node.set('id', index)
            if isinstance(node, Leaf):
                xml_node.set('terminal',
                             's{}_{}'.format(self.sentence_id, node.start_of_span))
            else:
                child_id = traverse(node.left_child)
                if not node.is_unary:
                    tmp = traverse(node.right_child)
                    child_id += ' ' + tmp
                xml_node.set('child',  child_id)
                xml_node.set('rule', node.rule)
            return index

        res = etree.Element('ccg')
        res.set('id', 's{}_ccg{}'.format(self.sentence_id, self.processed))
        res.set('root', str(traverse(tree)))
        self.processed += 1
        return res


def dummy_tokenize(sentences: List[List[str]],
                   dummy_tag: Optional[str] = None,
                   drop_sentence_text: bool = False) -> etree.Element:
    root_node = etree.Element('root')
    document_node = etree.SubElement(root_node, 'document')
    document_node.set('id', 'd0')
    sentences_node = etree.SubElement(document_node, 'sentences')
    for i, sentence in enumerate(sentences):
        sentence_node = etree.SubElement(sentences_node, 'sentence')
        sentence_node.set('id', 's{}'.format(i))
        if not drop_sentence_text:
            sentence_node.text = ''.join(sentence)
        tokens_node = etree.SubElement(sentence_node, 'tokens')
        tokens_node.set('annotators', 'dummy')
        offset = 0
        for j, token in enumerate(sentence):
            token_node = etree.SubElement(tokens_node, 'token')
            token_node.set('surf', token)
            token_node.set('base', token)
            token_node.set('id', 's{}_{}'.format(i, j))
            token_node.set('offsetBegin', str(offset))
            offset += len(token)
            token_node.set('offsetEnd', str(offset))
            if dummy_tag is not None:
                for label in ['pron', 'yomi', 'lemma', 'cForm',
                              'cType', 'pos3', 'pos2', 'pos1', 'pos']:
                    token_node.set(label, dummy_tag)
    return root_node


# TODO: use of external tokenizer & tagger?
tagging_cmd = 'java -Xmx4g -cp \"{}/*\" jigg.pipeline.Pipeline --annotators ssplit,kuromoji --file {}'


def jigg_tokenize(sentences: List[List[str]], jigg_jar_dir: str) -> etree.Element:
    tmp_file = tempfile.mktemp()
    with open(tmp_file, 'w') as f:
        for sentence in sentences:
            print(' '.join(sentence), file=f)
    command = tagging_cmd.format(jigg_jar_dir, tmp_file)
    proc = subprocess.Popen(command,
                            shell=True,
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    proc.communicate()
    with open(tmp_file + '.xml') as f:
        return etree.parse(f)


def main():
    parser = argparse.ArgumentParser('')
    parser.add_argument('FILE')
    parser.add_argument('-i',
                        '--skip-ill-formed',
                        action='store_true',
                        help='skip trees that contain a node whose arity > 2')
    parser.add_argument('-d',
                        '--drop-text',
                        action='store_true',
                        help='don\'t contain raw sentences in XML (useful for debugging)')
    args = parser.parse_args()

    trees = read_abc(args.FILE,
                     skip_ill_formed=args.skip_ill_formed)
    xml_results = dummy_tokenize([tree.tokens for tree in trees],
                                 dummy_tag='*',
                                 drop_sentence_text=args.drop_text)
    sentences = xml_results[0][0]
    for i, (sentence, tree) in enumerate(zip(sentences, trees)):
        runner = ABCToXML(i)
        sentence.append(runner.process(tree))
    print(etree.tostring(xml_results,
                         xml_declaration=True,
                         pretty_print=True,
                         encoding='utf-8').decode('utf-8'))


if __name__ == '__main__':
    main()
