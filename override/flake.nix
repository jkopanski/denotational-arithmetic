{
  description = "felix-arithmetic with local checkout of deps";
  
  inputs = {
    felix.url = "path:/home/nat/famisoft/felix";
    felix-boolean = {
      url = "path:/home/nat/famisoft/felix-boolean";
      inputs.felix.follows = "felix";
    };
    felix-arithmetic = {
      url = "..";
      inputs = {
        felix.follows = "felix";
        felix-boolean.follows = "felix-boolean";
      };
    };
  };

  outputs = { felix-arithmetic, ... }: felix-arithmetic.outputs;
}
