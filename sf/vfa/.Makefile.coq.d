Preface.vo Preface.glob Preface.v.beautified Preface.required_vo: Preface.v 
Preface.vio: Preface.v 
Preface.vos Preface.vok Preface.required_vos: Preface.v 
Perm.vo Perm.glob Perm.v.beautified Perm.required_vo: Perm.v 
Perm.vio: Perm.v 
Perm.vos Perm.vok Perm.required_vos: Perm.v 
Sort.vo Sort.glob Sort.v.beautified Sort.required_vo: Sort.v Perm.vo
Sort.vio: Sort.v Perm.vio
Sort.vos Sort.vok Sort.required_vos: Sort.v Perm.vos
Multiset.vo Multiset.glob Multiset.v.beautified Multiset.required_vo: Multiset.v Perm.vo Sort.vo
Multiset.vio: Multiset.v Perm.vio Sort.vio
Multiset.vos Multiset.vok Multiset.required_vos: Multiset.v Perm.vos Sort.vos
BagPerm.vo BagPerm.glob BagPerm.v.beautified BagPerm.required_vo: BagPerm.v Perm.vo Sort.vo
BagPerm.vio: BagPerm.v Perm.vio Sort.vio
BagPerm.vos BagPerm.vok BagPerm.required_vos: BagPerm.v Perm.vos Sort.vos
Selection.vo Selection.glob Selection.v.beautified Selection.required_vo: Selection.v Perm.vo Multiset.vo
Selection.vio: Selection.v Perm.vio Multiset.vio
Selection.vos Selection.vok Selection.required_vos: Selection.v Perm.vos Multiset.vos
Merge.vo Merge.glob Merge.v.beautified Merge.required_vo: Merge.v Perm.vo Sort.vo
Merge.vio: Merge.v Perm.vio Sort.vio
Merge.vos Merge.vok Merge.required_vos: Merge.v Perm.vos Sort.vos
Maps.vo Maps.glob Maps.v.beautified Maps.required_vo: Maps.v Perm.vo
Maps.vio: Maps.v Perm.vio
Maps.vos Maps.vok Maps.required_vos: Maps.v Perm.vos
SearchTree.vo SearchTree.glob SearchTree.v.beautified SearchTree.required_vo: SearchTree.v Perm.vo Maps.vo Sort.vo
SearchTree.vio: SearchTree.v Perm.vio Maps.vio Sort.vio
SearchTree.vos SearchTree.vok SearchTree.required_vos: SearchTree.v Perm.vos Maps.vos Sort.vos
ADT.vo ADT.glob ADT.v.beautified ADT.required_vo: ADT.v Perm.vo Maps.vo SearchTree.vo
ADT.vio: ADT.v Perm.vio Maps.vio SearchTree.vio
ADT.vos ADT.vok ADT.required_vos: ADT.v Perm.vos Maps.vos SearchTree.vos
Extract.vo Extract.glob Extract.v.beautified Extract.required_vo: Extract.v Perm.vo
Extract.vio: Extract.v Perm.vio
Extract.vos Extract.vok Extract.required_vos: Extract.v Perm.vos
Redblack.vo Redblack.glob Redblack.v.beautified Redblack.required_vo: Redblack.v Perm.vo Extract.vo
Redblack.vio: Redblack.v Perm.vio Extract.vio
Redblack.vos Redblack.vok Redblack.required_vos: Redblack.v Perm.vos Extract.vos
Trie.vo Trie.glob Trie.v.beautified Trie.required_vo: Trie.v Perm.vo Maps.vo
Trie.vio: Trie.v Perm.vio Maps.vio
Trie.vos Trie.vok Trie.required_vos: Trie.v Perm.vos Maps.vos
Priqueue.vo Priqueue.glob Priqueue.v.beautified Priqueue.required_vo: Priqueue.v Perm.vo
Priqueue.vio: Priqueue.v Perm.vio
Priqueue.vos Priqueue.vok Priqueue.required_vos: Priqueue.v Perm.vos
Binom.vo Binom.glob Binom.v.beautified Binom.required_vo: Binom.v Perm.vo Priqueue.vo
Binom.vio: Binom.v Perm.vio Priqueue.vio
Binom.vos Binom.vok Binom.required_vos: Binom.v Perm.vos Priqueue.vos
Decide.vo Decide.glob Decide.v.beautified Decide.required_vo: Decide.v Perm.vo
Decide.vio: Decide.v Perm.vio
Decide.vos Decide.vok Decide.required_vos: Decide.v Perm.vos
Color.vo Color.glob Color.v.beautified Color.required_vo: Color.v Perm.vo
Color.vio: Color.v Perm.vio
Color.vos Color.vok Color.required_vos: Color.v Perm.vos
PrefaceTest.vo PrefaceTest.glob PrefaceTest.v.beautified PrefaceTest.required_vo: PrefaceTest.v Preface.vo
PrefaceTest.vio: PrefaceTest.v Preface.vio
PrefaceTest.vos PrefaceTest.vok PrefaceTest.required_vos: PrefaceTest.v Preface.vos
PermTest.vo PermTest.glob PermTest.v.beautified PermTest.required_vo: PermTest.v Perm.vo
PermTest.vio: PermTest.v Perm.vio
PermTest.vos PermTest.vok PermTest.required_vos: PermTest.v Perm.vos
SortTest.vo SortTest.glob SortTest.v.beautified SortTest.required_vo: SortTest.v Sort.vo
SortTest.vio: SortTest.v Sort.vio
SortTest.vos SortTest.vok SortTest.required_vos: SortTest.v Sort.vos
MultisetTest.vo MultisetTest.glob MultisetTest.v.beautified MultisetTest.required_vo: MultisetTest.v Multiset.vo
MultisetTest.vio: MultisetTest.v Multiset.vio
MultisetTest.vos MultisetTest.vok MultisetTest.required_vos: MultisetTest.v Multiset.vos
BagPermTest.vo BagPermTest.glob BagPermTest.v.beautified BagPermTest.required_vo: BagPermTest.v BagPerm.vo
BagPermTest.vio: BagPermTest.v BagPerm.vio
BagPermTest.vos BagPermTest.vok BagPermTest.required_vos: BagPermTest.v BagPerm.vos
SelectionTest.vo SelectionTest.glob SelectionTest.v.beautified SelectionTest.required_vo: SelectionTest.v Selection.vo
SelectionTest.vio: SelectionTest.v Selection.vio
SelectionTest.vos SelectionTest.vok SelectionTest.required_vos: SelectionTest.v Selection.vos
MergeTest.vo MergeTest.glob MergeTest.v.beautified MergeTest.required_vo: MergeTest.v Merge.vo
MergeTest.vio: MergeTest.v Merge.vio
MergeTest.vos MergeTest.vok MergeTest.required_vos: MergeTest.v Merge.vos
MapsTest.vo MapsTest.glob MapsTest.v.beautified MapsTest.required_vo: MapsTest.v Maps.vo
MapsTest.vio: MapsTest.v Maps.vio
MapsTest.vos MapsTest.vok MapsTest.required_vos: MapsTest.v Maps.vos
SearchTreeTest.vo SearchTreeTest.glob SearchTreeTest.v.beautified SearchTreeTest.required_vo: SearchTreeTest.v SearchTree.vo
SearchTreeTest.vio: SearchTreeTest.v SearchTree.vio
SearchTreeTest.vos SearchTreeTest.vok SearchTreeTest.required_vos: SearchTreeTest.v SearchTree.vos
ADTTest.vo ADTTest.glob ADTTest.v.beautified ADTTest.required_vo: ADTTest.v ADT.vo
ADTTest.vio: ADTTest.v ADT.vio
ADTTest.vos ADTTest.vok ADTTest.required_vos: ADTTest.v ADT.vos
ExtractTest.vo ExtractTest.glob ExtractTest.v.beautified ExtractTest.required_vo: ExtractTest.v Extract.vo
ExtractTest.vio: ExtractTest.v Extract.vio
ExtractTest.vos ExtractTest.vok ExtractTest.required_vos: ExtractTest.v Extract.vos
RedblackTest.vo RedblackTest.glob RedblackTest.v.beautified RedblackTest.required_vo: RedblackTest.v Redblack.vo
RedblackTest.vio: RedblackTest.v Redblack.vio
RedblackTest.vos RedblackTest.vok RedblackTest.required_vos: RedblackTest.v Redblack.vos
TrieTest.vo TrieTest.glob TrieTest.v.beautified TrieTest.required_vo: TrieTest.v Trie.vo
TrieTest.vio: TrieTest.v Trie.vio
TrieTest.vos TrieTest.vok TrieTest.required_vos: TrieTest.v Trie.vos
PriqueueTest.vo PriqueueTest.glob PriqueueTest.v.beautified PriqueueTest.required_vo: PriqueueTest.v Priqueue.vo
PriqueueTest.vio: PriqueueTest.v Priqueue.vio
PriqueueTest.vos PriqueueTest.vok PriqueueTest.required_vos: PriqueueTest.v Priqueue.vos
BinomTest.vo BinomTest.glob BinomTest.v.beautified BinomTest.required_vo: BinomTest.v Binom.vo
BinomTest.vio: BinomTest.v Binom.vio
BinomTest.vos BinomTest.vok BinomTest.required_vos: BinomTest.v Binom.vos
DecideTest.vo DecideTest.glob DecideTest.v.beautified DecideTest.required_vo: DecideTest.v Decide.vo
DecideTest.vio: DecideTest.v Decide.vio
DecideTest.vos DecideTest.vok DecideTest.required_vos: DecideTest.v Decide.vos
ColorTest.vo ColorTest.glob ColorTest.v.beautified ColorTest.required_vo: ColorTest.v Color.vo
ColorTest.vio: ColorTest.v Color.vio
ColorTest.vos ColorTest.vok ColorTest.required_vos: ColorTest.v Color.vos
