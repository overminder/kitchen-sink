import * as React from 'react';

export class Index extends React.Component {
  constructor(props) {
    super(props);
  }

  getNumber() {
    return 5;
  }

  render() {
    return (
      <div>
        {this.getNumber()}
        <h1>Hello, world</h1>
      </div>
    );
  }
}
