## Requirements

* Python >= 3.6.0
* lxml == 4.2.5
* nltk == 3.4.5
* Coq == 8.6

## Extract unproven terms

```
./ja/rte_ja_sg.sh <sentences.txt> <semantic_templates.yaml>
```

## Bidirectional reasoning (select parser, depccg or jigg)

```
./ja/rte_ja_bi.sh <sentences.txt> <semantic_templates.yaml> <parser>
```
