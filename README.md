# Merging Noisy Ontologies from An Original Ontology

We propose a noisy ontology merging framework 
to detect new information from an original ontology, motivated by the assessment of the merging models and the need to identify hidden-finding links in an ontology. 
The main goal of the work is to discover new rules, complete the ontology and evaluate the merging models. 
To this end, we generate the noisy ontologies from an original ontology based on tree structure edit operations. 
Then, we take advantage of the power of existing ontology merging methods to exploit the potential relations between concepts.

How to run the Noisy Ontology Merging:
For Method 1 (Model-Based Merging)
```
python3 NoisyTree_MergingOntologies_ver7.py

```

For Method 2 (QCN-Based Merging)
```
python3 NoisyTree_MergingOntologiesWithQCNs.py

```

## Merged Result of Conference Ontology:

![Image 1](ResultHuman.PNG)

## Merged Result of Human Ontology:

![Image 2](Ex-PersonConference4.PNG)