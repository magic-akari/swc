class Class {
    method() {
        return _async_to_generator(function*() {
            var _this = this;
            this;
            (function() {
                return _this;
            });
            (function() {
                _this;
                (function() {
                    return _this;
                });
                function x() {
                    var _this = this;
                    this;
                    (function() {
                        _this;
                    });
                    (function() {
                        return _async_to_generator(function*() {
                            _this;
                        })();
                    });
                }
            });
            function x() {
                var _this = this;
                this;
                (function() {
                    _this;
                });
                (function() {
                    return _async_to_generator(function*() {
                        _this;
                    })();
                });
            }
        }).call(this);
    }
}
