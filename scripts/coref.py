import spacy
import neuralcoref
import sys
import json
from dataclasses import dataclass
from typing import List

@dataclass
class Span:
    start: int
    end: int
    line_num: int
    text: str

@dataclass
class Coref:
    main: Span
    mentions: List[Span]

def first_gt(sorted_list, i):
    result = 0
    while result < len(sorted_list):
        if(sorted_list[result] > i):
            break
        else:
            result += 1
    return result

def word_to_span(word, token_nums):
    ith_sentence = first_gt(token_nums, word.start)
    tokens_diff = 0 if ith_sentence == 0 else token_nums[ith_sentence - 1]
    return Span(
        word.start - tokens_diff,
        word.end - tokens_diff,
        ith_sentence,
        str(word)
    )

def serialize_span(span):
    return {
        'start': span.start,
        'end': span.end,
        'line_num': span.line_num,
        'text': span.text
    }

def serialize_coref(coref):
    return {
        'main': serialize_span(coref.main),
        'mentions': [serialize_span(mention) for mention in coref.mentions]
    }

def compose_coref(cluster, token_nums):
    mention_spans = []
    for mention in cluster.mentions:
        if str(mention) == str(cluster.main) and mention.start == cluster.main.start:
            continue
        mention_spans.append(word_to_span(mention, token_nums))
    coref = Coref(
        word_to_span(cluster.main, token_nums),
        mention_spans
    )
    return serialize_coref(coref)

def main():
    tok_file = sys.argv[1]
    nlp = spacy.load('en')
    neuralcoref.add_to_pipe(nlp)
    with open(tok_file, 'r') as f:
        lines = f.readlines()
    hypothesis_lines = lines[:-1]
    hypothesis_token_nums = []
    hypothesis = ""
    prev_tokens = 0
    for line in hypothesis_lines:
        hypothesis_token_nums.append(len(line.strip().split(' ')) + prev_tokens)
        prev_tokens = hypothesis_token_nums[-1]
        hypothesis += line.strip() + ' '
    conclusion = lines[-1].strip()
    conclusion_token_nums = [len(conclusion.split(' '))]
    hypothesis_doc = nlp(hypothesis)
    conclusion_doc = nlp(conclusion)

    hypothesis_coref = [compose_coref(c, hypothesis_token_nums) for c in hypothesis_doc._.coref_clusters]
    conclusion_coref = [compose_coref(c, conclusion_token_nums) for c in conclusion_doc._.coref_clusters]
    print(
        json.dumps({
            "hypothesis": hypothesis_coref,
            "conclusion": conclusion_coref
        },
        indent=4)
    )

if __name__ == '__main__':
	main()