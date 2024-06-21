The content is in FldNumCom.m, and tests are in test_FldNumCom.m.

The file Embeddings.m is a file that we have in the HilbertModularForms package that may be of interest
so I included it here. The output of Magma's `InfinitePlace(K)` function is actually a list of embeddings,
one representing each place, and this conflict of terminology led to some annoyances for us.
It's also nice sometimes easily be able able to work with all the embeddings rather than all 
the places. I didn't use it in the FldNumCom file but it would be easy to add. 
