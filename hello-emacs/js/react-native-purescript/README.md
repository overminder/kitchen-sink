The bads:

- extensible records not so extensible. missing row constraints and
  type equality. ps-foreign-options and ps-react's solutions not
  good enough.

- Eff monad too burdensome and doesn't play well with records, e.g.
  can't use have a record that contains a React.readState action.

- compilation too slow. makes flycheck literally unusable.
