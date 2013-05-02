from FuXi.Horn.HornRules import HornFromN3
rules = HornFromN3(
    'http://www.agfa.com/w3c/euler/rdfs-rules.n3')
for rule in rules:
    print(rule)
