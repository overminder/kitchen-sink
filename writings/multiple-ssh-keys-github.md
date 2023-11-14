### Option 1: Add all SSH keys to ssh_config

See https://stackoverflow.com/a/33228296

This is a brute force way of using multiple SSH keys. ssh-client will
try each key until it succeeds.
- pros: Easy to setup
- cons:
  + Doesn't work with github, since [github uses a 2-step authentication](https://stackoverflow.com/questions/2419566/best-way-to-use-multiple-ssh-private-keys-on-one-client#comment79297973_33228296).
  + Repeated failed tries may [result in ban](https://stackoverflow.com/questions/2419566/best-way-to-use-multiple-ssh-private-keys-on-one-client#comment98162745_33228296)

### Option 2: Use per-host key config

See https://stackoverflow.com/a/23751734

- pros: Works with github
- cons: Doesn't work by default if any of the key is added to ssh-agent.
  Setting IdentityAgent=none works around this.

### Option 3: Use a script to manually switch key and user

[See this gist](https://gist.github.com/jexchan/2351996?permalink_comment_id=4629226#gistcomment-4629226)

- pros: fully customizable
- cons: this is a bit too manual

