# EZNF

This library is designed to speed-up prototyping encodings, especiall for combinatorial problems.

## Modeler

The main abstraction of the library is the so-called `modeler`.

Therefore we will always start with:

```python
import modeler

Z = modeler.Modeler()
```

Then, we will use the `Z` modeler variable to *model* the problem.

For example, we can use
```python
Z.add_var(f'v_{i}', f'vertex {i} is selected for the CLIQUE')
```


## Tests

```
python3 -m pytest
```
