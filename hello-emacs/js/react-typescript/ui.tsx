import {
  Component,
} from "react";

type Hello = {
  hello: string
};

export class Index extends Component<Hello, any> {
  render() {
    let a: string = this.props.hello;
    return (
      <div>{this.props.hello}</div>
    );
  }
}

const i = <Index hello={"asdf"} />;
