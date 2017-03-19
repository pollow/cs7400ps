;; Chang Xing, Ruiyang Xu
;; xing.ch@husky.neu.edu, xu.r@husky.neu.edu

In the metafiction translate, we choose to use the union language:
(define-union-language ST (s. LamBool) (t. Lam))

The reason is that we don't want the translate function to confuse on the syntax of
input language and output language. So that it will only accept LamBool as its input
language and output in Lam language.