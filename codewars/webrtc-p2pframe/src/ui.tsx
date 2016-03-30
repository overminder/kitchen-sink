import * as React from 'react';

import { RtcState } from './rtc';

function valueOfEvent(e: {target: EventTarget}): any {
  return (e.target as any).value;
}

export class Form extends React.Component<void, {value: string}> {
  constructor() {
    super();
    this.state = {
      value: null,
    };
  }

  handleChange_(e: React.FormEvent) {
    this.setState({
      value: valueOfEvent(e),
    });
  }

  async onSubmit_(key: string) {
    console.log('onSubmit', key);
    let state: RtcState;
    if (key) {
      state = await RtcState.connect(key);
      console.log('connect ok');
      state.ch.send('HAI from client');
      state.ch.send('HAI from client2');
      state.ch.send('HAI from client3');
    } else {
      state = await RtcState.bind();
      console.log('bind key', state.key);
      this.setState({value: state.key});
      console.log('start accepting loop');
      await state.accept();
      console.log('accept ok', state.conn.signalingState);
      state.ch.send('HAI from server');
      state.ch.send('HAI from server2');
      state.ch.send('HAI from server3');
    }
    (window as any).ch = state.ch;
  }

  render() {
    const onSubmit = () => this.onSubmit_(this.state.value);

    return (
      <div>
        <button onClick={onSubmit}>Serve or connect</button>
        <br />

        <div>Key1: </div>
        <input
          type='text'
          value={this.state.value || ''}
          onSubmit={onSubmit}
          onChange={(e) => this.handleChange_(e)} />
      </div>
    );
  }
}
